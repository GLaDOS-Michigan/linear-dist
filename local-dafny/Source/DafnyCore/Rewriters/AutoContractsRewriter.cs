using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// AutoContracts is an experimental feature that will fill much of the dynamic-frames boilerplate
/// into a class.  From the user's perspective, what needs to be done is simply:
///  - mark the class with {:autocontracts}
///  - declare a function (or predicate) called Valid()
///
/// AutoContracts will then:
///
/// Declare, unless there already exist members with these names:
///    ghost var Repr: set(object)
///    predicate Valid()
///
/// For function/predicate Valid(), insert:
///    reads this, Repr
///    ensures Valid() ==> this in Repr
/// Into body of Valid(), insert (at the beginning of the body):
///    this in Repr && null !in Repr
/// and also insert, for every array-valued field A declared in the class:
///    (A != null ==> A in Repr) &&
/// and for every field F of a class type T where T has a field called Repr, also insert:
///    (F != null ==> F in Repr && F.Repr SUBSET Repr && this !in Repr && F.Valid())
/// Except, if A or F is declared with {:autocontracts false}, then the implication will not
/// be added.
///
/// For every constructor, add:
///    ensures Valid() && fresh(Repr)
/// At the end of the body of the constructor, add:
///    Repr := {this};
///    if (A != null) { Repr := Repr + {A}; }
///    if (F != null) { Repr := Repr + {F} + F.Repr; }
///
/// In all the following cases, no "modifies" clause or "reads" clause is added if the user
/// has given one.
///
/// For every non-static non-ghost method that is not a "simple query method",
/// add:
///    requires Valid()
///    modifies Repr
///    ensures Valid() && fresh(Repr - old(Repr))
/// At the end of the body of the method, add:
///    if (A != null && !(A in Repr)) { Repr := Repr + {A}; }
///    if (F != null && !(F in Repr && F.Repr SUBSET Repr)) { Repr := Repr + {F} + F.Repr; }
/// For every non-static non-twostate method that is either ghost or is a "simple query method",
/// add:
///    requires Valid()
/// For every non-static twostate method, add:
///    requires old(Valid())
///
/// For every non-"Valid" non-static function, add:
///    requires Valid()
///    reads Repr
/// </summary>
public class AutoContractsRewriter : IRewriter {
  private SystemModuleManager systemModuleManager;
  public AutoContractsRewriter(ErrorReporter reporter)
    : base(reporter) {
    Contract.Requires(reporter != null);
    Contract.Requires(systemModuleManager != null);
  }

  internal override void PreResolve(Program program) {
    systemModuleManager = program.SystemModuleManager;
  }

  internal override void PreResolve(ModuleDefinition m) {
    foreach (var d in m.TopLevelDecls) {
      bool sayYes = true;
      if (d is ClassLikeDecl && Attributes.ContainsBool(d.Attributes, "autocontracts", ref sayYes) && sayYes) {
        ProcessClassPreResolve((TopLevelDeclWithMembers)d);
      }
    }
  }

  void ProcessClassPreResolve(TopLevelDeclWithMembers cl) {
    var range = cl.NameNode.RangeToken.MakeAutoGenerated();
    // Add:  ghost var Repr: set<object>
    // ...unless a field with that name is already present
    if (!cl.Members.Exists(member => member is Field && member.Name == "Repr")) {
      Type ty = new SetType(true, systemModuleManager.ObjectQ());
      var repr = new Field(range, new Name(range, "Repr"), true, ty, null);
      cl.Members.Add(repr);
      AddHoverText(cl.tok, "{0}", Printer.FieldToString(Reporter.Options, repr));
    }
    // Add:  predicate Valid()
    // ...unless an instance function with that name is already present
    if (!cl.Members.Exists(member => member is Function && member.Name == "Valid" && !member.IsStatic)) {
      var valid = new Predicate(range, new Name(cl.NameNode.RangeToken, "Valid"), false, true, false, new List<TypeParameter>(), new List<Formal>(), null,
        new List<AttributedExpression>(), new List<FrameExpression>(), new List<AttributedExpression>(), new Specification<Expression>(new List<Expression>(), null),
        null, Predicate.BodyOriginKind.OriginalOrInherited, null, null, null, null);
      cl.Members.Add(valid);
      // It will be added to hover text later
    }

    foreach (var member in cl.Members) {
      bool sayYes = true;
      if (Attributes.ContainsBool(member.Attributes, "autocontracts", ref sayYes) && !sayYes) {
        // the user has excluded this member
        continue;
      }
      if (member.RefinementBase != null) {
        // member is inherited from a module where it was already processed
        continue;
      }
      IToken tok = new AutoGeneratedToken(member.tok);
      if (member is Function && member.Name == "Valid" && !member.IsStatic) {
        var valid = (Function)member;
        // reads this, Repr
        var r0 = new ThisExpr(tok);
        var r1 = CreateUnresolvedThisRepr(tok);
        valid.Reads.Add(new FrameExpression(tok, r0, null));
        valid.Reads.Add(new FrameExpression(tok, r1, null));
        // ensures Valid() ==> this in Repr
        var post = new BinaryExpr(tok, BinaryExpr.Opcode.Imp,
          CreateUnresolvedValidCall(tok),
          new BinaryExpr(tok, BinaryExpr.Opcode.In,
            new ThisExpr(tok),
            CreateUnresolvedThisRepr(tok)));
        valid.Ens.Insert(0, new AttributedExpression(post));
        if (member.tok == cl.tok) {
          // We added this function above, so produce a hover text for the entire function signature
          AddHoverText(cl.tok, "{0}", Printer.FunctionSignatureToString(Reporter.Options, valid));
        } else {
          AddHoverText(member.tok, "reads {0}, {1}\nensures {2}", r0, r1, post);
        }
      } else if (member is Function && !member.IsStatic) {
        var f = (Function)member;
        // requires Valid()
        var valid = CreateUnresolvedValidCall(tok);
        f.Req.Insert(0, new AttributedExpression(valid));
        var format = "requires {0}";
        var repr = CreateUnresolvedThisRepr(tok);
        if (f.Reads.Count == 0) {
          // reads Repr
          f.Reads.Add(new FrameExpression(tok, repr, null));
          format += "\nreads {1}";
        }
        AddHoverText(member.tok, format, valid, repr);
      } else if (member is Constructor) {
        var ctor = (Constructor)member;
        // ensures Valid();
        var valid = CreateUnresolvedValidCall(tok);
        ctor.Ens.Insert(0, new AttributedExpression(valid));
        // ensures fresh(Repr);
        var freshness = new FreshExpr(tok, CreateUnresolvedThisRepr(tok));
        ctor.Ens.Insert(1, new AttributedExpression(freshness));
        var m0 = new ThisExpr(tok);
        AddHoverText(member.tok, "modifies {0}\nensures {1} && {2}", m0, valid, freshness);
      }
    }
  }

  internal override void PostResolveIntermediate(ModuleDefinition m) {
    foreach (var d in m.TopLevelDecls) {
      bool sayYes = true;
      if (d is ClassLikeDecl && Attributes.ContainsBool(d.Attributes, "autocontracts", ref sayYes) && sayYes) {
        ProcessClassPostResolve((ClassLikeDecl)d);
      }
    }
  }

  void ProcessClassPostResolve(ClassLikeDecl cl) {
    // Find all fields of a reference type, and make a note of whether or not the reference type has a Repr field.
    // Also, find the Repr field and the function Valid in class "cl"
    Field ReprField = null;
    Function Valid = null;
    var subobjects = new List<Tuple<Field, Field, Function>>();
    foreach (var member in cl.Members) {
      var field = member as Field;
      if (field != null) {
        var sayYes = true;
        if (field.Name == "Repr") {
          ReprField = field;
        } else if (Attributes.ContainsBool(field.Attributes, "autocontracts", ref sayYes) && !sayYes) {
          // ignore this field
        } else if (field.Type.IsRefType) {
          var rcl = (ClassLikeDecl)((UserDefinedType)field.Type.NormalizeExpand()).ResolvedClass;
          Field rRepr = null;
          Function rValid = null;
          foreach (var memb in rcl.Members) {
            if (memb is Field { Name: "Repr" } f) {
              var t = f.Type.AsSetType;
              if (t != null && t.Arg.IsObjectQ) {
                rRepr = f;
              }
            } else if (memb is Function { IsStatic: false, Name: "Valid" } fn) {
              if (fn.Formals.Count == 0 && fn.ResultType.IsBoolType) {
                rValid = fn;
              }
            }
            if (rRepr != null && rValid != null) {
              break;
            }
          }
          subobjects.Add(new Tuple<Field, Field, Function>(field, rRepr, rValid));
        }
      } else if (member is Function { IsStatic: false, Name: "Valid" } validFunction) {
        if (validFunction.Formals.Count == 0 && validFunction.ResultType.IsBoolType) {
          Valid = validFunction;
        }
      }
    }
    Contract.Assert(ReprField != null);  // we expect there to be a "Repr" field, since we added one in PreResolve

    IToken clTok = new AutoGeneratedToken(cl.tok);
    Type ty = ModuleResolver.GetThisType(clTok, cl);
    var self = new ThisExpr(clTok) {
      Type = ty
    };
    var implicitSelf = new ImplicitThisExpr(clTok) {
      Type = ty
    };
    var Repr = CreateResolvedFieldSelect(clTok, implicitSelf, ReprField);

    foreach (var member in cl.Members) {
      bool sayYes = true;
      if (Attributes.ContainsBool(member.Attributes, "autocontracts", ref sayYes) && !sayYes) {
        continue;
      }
      IToken tok = new AutoGeneratedToken(member.tok);
      if (member is Function && member.Name == "Valid" && !member.IsStatic) {
        var valid = (Function)member;
        var validConjuncts = new List<Expression>();
        if (valid.IsGhost && valid.ResultType.IsBoolType) {
          if (valid.RefinementBase == null) {
            var c0 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.InSet, self, Repr);  // this in Repr
            var c1 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.NotInSet, new LiteralExpr(tok) { Type = systemModuleManager.ObjectQ() }, Repr);  // null !in Repr
            var c = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c0, c1);
            validConjuncts.Add(c);
          }

          foreach (var ff in subobjects) {
            if (ff.Item1.RefinementBase != null) {
              // the field has been inherited from a refined module, so don't include it here
              continue;
            }
            var F = CreateResolvedFieldSelect(tok, implicitSelf, ff.Item1);
            var c0 = IsNotNull(tok, F);
            var c1 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.InSet, F, Repr);
            if (ff.Item2 == null) {
              // F != null ==> F in Repr  (so, nothing else to do)
            } else {
              // F != null ==> F in Repr && F.Repr <= Repr && this !in F.Repr && F.Valid()
              var FRepr = CreateResolvedFieldSelect(tok, F, ff.Item2);
              var c2 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.Subset, FRepr, Repr);
              var c3 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.NotInSet, self, FRepr);
              c1 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c1,
                BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c2, c3));
              if (ff.Item3 != null) {
                // F.Valid()
                c1 = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c1,
                  CreateResolvedValidCall(tok, F, ff.Item3, valid));
              }
            }
            validConjuncts.Add(Expression.CreateImplies(c0, c1));
          }

          var hoverText = "";
          var sep = "";
          if (valid.Body == null) {
            valid.Body = Expression.CreateBoolLiteral(tok, true);
            if (validConjuncts.Count == 0) {
              hoverText = "true";
              sep = "\n";
            }
          }
          for (int i = validConjuncts.Count; 0 <= --i;) {
            var c = validConjuncts[i];
            valid.Body = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.And, c, valid.Body);
            hoverText = Printer.ExprToString(Reporter.Options, c) + sep + hoverText;
            sep = "\n";
          }
          AddHoverText(valid.tok, "{0}", hoverText);
        }

      } else if (member is Constructor) {
        var ctor = (Constructor)member;
        if (ctor.Body != null) {
          var sbs = (DividedBlockStmt)ctor.Body;
          var n = sbs.Body.Count;
          if (ctor.RefinementBase == null) {
            // Repr := {this};
            var e = new SetDisplayExpr(tok, true, new List<Expression>() { self });
            e.Type = new SetType(true, systemModuleManager.ObjectQ());
            Statement s = new AssignStmt(member.RangeToken, Repr, new ExprRhs(e));
            s.IsGhost = true;
            sbs.AppendStmt(s);
          }
          AddSubobjectReprs(tok, ctor.RangeToken.EndToken, subobjects, sbs, n, implicitSelf, Repr);
        }

      } else if (member is Method && !member.IsStatic && Valid != null) {
        var m = (Method)member;
        var addStatementsToUpdateRepr = false;
        if (member.IsGhost || IsSimpleQueryMethod(m)) {
          if (m.RefinementBase == null) {
            // requires Valid()
            var valid = CreateResolvedValidCall(tok, implicitSelf, Valid, m);
            if (m is TwoStateLemma) {
              // Instead use:  requires old(Valid())
              valid = new OldExpr(tok, valid);
              valid.Type = Type.Bool;
            }
            m.Req.Insert(0, new AttributedExpression(valid));
            AddHoverText(member.tok, "requires {0}", valid);
          }
        } else if (m.RefinementBase == null) {
          // requires Valid()
          var valid = CreateResolvedValidCall(tok, implicitSelf, Valid, m);
          m.Req.Insert(0, new AttributedExpression(valid));
          var format = "requires {0}";
          if (m.Mod.Expressions.Count == 0) {
            // modifies Repr
            m.Mod.Expressions.Add(new FrameExpression(Repr.tok, Repr, null));
            format += "\nmodifies {1}";
            addStatementsToUpdateRepr = true;
          }
          // ensures Valid()
          m.Ens.Insert(0, new AttributedExpression(valid));
          // ensures fresh(Repr - old(Repr));
          var e0 = new OldExpr(tok, Repr);
          e0.Type = Repr.Type;
          var e1 = new BinaryExpr(tok, BinaryExpr.Opcode.Sub, Repr, e0);
          e1.ResolvedOp = BinaryExpr.ResolvedOpcode.SetDifference;
          e1.Type = Repr.Type;
          var freshness = new FreshExpr(tok, e1);
          freshness.Type = Type.Bool;
          m.Ens.Insert(1, new AttributedExpression(freshness));
          AddHoverText(m.tok, format + "\nensures {0} && {2}", valid, Repr, freshness);
        } else {
          addStatementsToUpdateRepr = true;
        }

        if (addStatementsToUpdateRepr && m.Body != null) {
          var methodBody = (BlockStmt)m.Body;
          AddSubobjectReprs(tok, methodBody.RangeToken.EndToken, subobjects, methodBody, methodBody.Body.Count, implicitSelf, Repr);
        }
      }
    }
  }

  void AddSubobjectReprs(IToken tok, IToken endCurlyTok, List<Tuple<Field, Field, Function>> subobjects, BlockStmt block, int hoverTextFromHere,
    Expression implicitSelf, Expression Repr) {
    Contract.Requires(tok != null);
    Contract.Requires(endCurlyTok != null);
    Contract.Requires(subobjects != null);
    Contract.Requires(block != null);
    Contract.Requires(0 <= hoverTextFromHere && hoverTextFromHere <= block.Body.Count);
    Contract.Requires(implicitSelf != null);
    Contract.Requires(Repr != null);
    // TODO: these assignments should be included on every return path

    foreach (var ff in subobjects) {
      var F = CreateResolvedFieldSelect(tok, implicitSelf, ff.Item1);  // create a resolved MemberSelectExpr
      Expression e = new SetDisplayExpr(tok, true, new List<Expression>() { F }) {
        Type = new SetType(true, systemModuleManager.ObjectQ())  // resolve here
      };
      var rhs = new BinaryExpr(tok, BinaryExpr.Opcode.Add, Repr, e) {
        ResolvedOp = BinaryExpr.ResolvedOpcode.Union,
        Type = Repr.Type
      };
      Expression nguard = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.InSet, F, Repr);  // F in Repr
      if (ff.Item2 == null) {
        // Repr := Repr + {F}  (so, nothing else to do)
      } else {
        // Repr := Repr + {F} + F.Repr
        var FRepr = CreateResolvedFieldSelect(tok, F, ff.Item2);  // create resolved MemberSelectExpr
        rhs = new BinaryExpr(tok, BinaryExpr.Opcode.Add, rhs, FRepr) {
          ResolvedOp = BinaryExpr.ResolvedOpcode.Union,
          Type = Repr.Type
        };
        var ng = BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.Subset, FRepr, Repr);  // F.Repr <= Repr
        nguard = Expression.CreateAnd(nguard, ng);
      }
      // Repr := Repr + ...;
      Statement s = new AssignStmt(tok.ToRange(), Repr, new ExprRhs(rhs));
      s.IsGhost = true;
      // wrap if statement around s
      e = Expression.CreateAnd(IsNotNull(tok, F), Expression.CreateNot(tok, nguard));
      var thn = new BlockStmt(tok.ToRange(), new List<Statement>() { s });
      thn.IsGhost = true;
      s = new IfStmt(tok.ToRange(), false, e, thn, null);
      s.IsGhost = true;
      // finally, add s to the block
      block.AppendStmt(s);
    }
    if (hoverTextFromHere != block.Body.Count) {
      var hoverText = "";
      var sep = "";
      for (int i = hoverTextFromHere; i < block.Body.Count; i++) {
        hoverText += sep + Printer.StatementToString(Reporter.Options, block.Body[i]);
        sep = "\n";
      }
      AddHoverText(endCurlyTok, "{0}", hoverText);
    }
  }

  /// <summary>
  /// Returns an expression denoting "expr != null".  If the type
  /// of "expr" already implies "expr" is non-null, then an expression
  /// denoting "true" is returned.
  /// </summary>
  Expression IsNotNull(IToken tok, Expression expr) {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    if (expr.Type.IsNonNullRefType) {
      return Expression.CreateBoolLiteral(tok, true);
    } else {
      var cNull = new LiteralExpr(tok);
      cNull.Type = expr.Type;
      return BinBoolExpr(tok, BinaryExpr.ResolvedOpcode.NeqCommon, expr, cNull);
    }
  }

  bool IsSimpleQueryMethod(Method m) {
    // A simple query method has out parameters, its body has no effect other than to assign to them,
    // and the postcondition does not explicitly mention the pre-state.
    return m.Outs.Count != 0 && m.Body != null && LocalAssignsOnly(m.Body) &&
           m.Ens.TrueForAll(mfe => !MentionsOldState(mfe.E));
  }

  bool LocalAssignsOnly(Statement s) {
    Contract.Requires(s != null);
    if (s is AssignStmt) {
      var ss = (AssignStmt)s;
      return ss.Lhs.Resolved is IdentifierExpr;
    } else if (s is ConcreteUpdateStatement) {
      var ss = (ConcreteUpdateStatement)s;
      return ss.Lhss.TrueForAll(e => e.Resolved is IdentifierExpr);
    } else if (s is CallStmt) {
      return false;
    } else {
      foreach (var ss in s.SubStatements) {
        if (!LocalAssignsOnly(ss)) {
          return false;
        }
      }
    }
    return true;
  }

  /// <summary>
  /// Returns true iff 'expr' is a two-state expression, that is, if it mentions "old/fresh/unchanged(...)".
  /// </summary>
  static bool MentionsOldState(Expression expr) {
    Contract.Requires(expr != null);
    if (expr is OldExpr || expr is UnchangedExpr || expr is FreshExpr) {
      return true;
    }
    foreach (var ee in expr.SubExpressions) {
      if (MentionsOldState(ee)) {
        return true;
      }
    }
    return false;
  }

  private static Expression CreateUnresolvedThisRepr(IToken tok) {
    return new ExprDotName(tok, new ImplicitThisExpr(tok), "Repr", null);
  }

  public static Expression CreateUnresolvedValidCall(IToken tok) {
    return new ApplySuffix(tok, null,
      new ExprDotName(tok, new ImplicitThisExpr(tok), "Valid", null),
      new List<ActualBinding>(), tok);
  }

  /// <summary>
  /// Returns a resolved expression of the form "receiver.Valid()"
  /// </summary>
  public Expression CreateResolvedValidCall(IToken tok, Expression receiver, Function Valid, ICallable callingContext) {
    Contract.Requires(tok != null);
    Contract.Requires(receiver != null);
    Contract.Requires(Valid != null);
    Contract.Requires(callingContext != null);
    Contract.Requires(receiver.Type.NormalizeExpand() is UserDefinedType udt && udt.ResolvedClass == Valid.EnclosingClass);
    Contract.Requires(receiver.Type.NormalizeExpand().TypeArgs.Count == Valid.EnclosingClass.TypeArgs.Count);

    callingContext.EnclosingModule.CallGraph.AddEdge((ICallable)CodeContextWrapper.Unwrap(callingContext), Valid);
    return Expression.CreateResolvedCall(tok, receiver, Valid, new List<Expression>(), new List<Type>(), systemModuleManager);
  }

  public static Expression CreateResolvedFieldSelect(IToken tok, Expression receiver, Field field) {
    var memberSelectExpr = new MemberSelectExpr(tok, receiver, field);
    return new ExprDotName(tok, receiver, field.Name, null) {
      ResolvedExpression = memberSelectExpr,
      Type = memberSelectExpr.Type
    };
  }

  public static BinaryExpr BinBoolExpr(IToken tok, BinaryExpr.ResolvedOpcode rop, Expression e0, Expression e1) {
    var p = new BinaryExpr(tok, BinaryExpr.ResolvedOp2SyntacticOp(rop), e0, e1);
    p.ResolvedOp = rop;  // resolve here
    p.Type = Type.Bool;  // resolve here
    return p;
  }

  void AddHoverText(IToken tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    for (int i = 0; i < args.Length; i++) {
      if (args[i] is Expression) {
        args[i] = Printer.ExprToString(Reporter.Options, (Expression)args[i]);
      }
    }
    var s = "autocontracts:\n" + string.Format(format, args);
    Reporter.Info(MessageSource.Rewriter, tok, s.Replace("\n", "\n  "));
  }
}