SEND_PREDICATE_KEYWORD = "sendPredicate"

commons = {
"InitImpliesMessageInv": 
"""lemma InitImpliesMessageInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures MessageInv(c, v)
{
    InitImpliesValidVariables(c, v);
}""",

"MessageInvInductiveHeader":
"""lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')""",
}

includes = ["spec.dfy"]
imports = ["Types", "UtilitiesLibrary", "DistributedSystem", "Obligations"]


class SendPredicate:
    def __init__(self, module_name: str, name = "sp_name", hosts_field = "hosts", msg_cons ="Msg"):
        self.name = name
        self.module_name = module_name
        self.hosts_field = hosts_field
        self.msg_cons = msg_cons

    def get_invariant_name(self):
        return f"{self.name}Validity"
    
    def get_lemma_name(self):
        return f"InvNext{self.name}Validity"

    def to_dafny_invariant(self):
        res = []
        res.append(f"ghost predicate {self.get_invariant_name()}(c: Constants, v: Variables)")
        res.append("  requires v.WF(c)")
        res.append("  requires ValidMessages(c, v)")
        res.append("{")
        res.append(f"  forall msg | msg in v.network.sentMsgs && msg.{self.msg_cons}?")
        res.append("  ::")
        res.append("  (exists i ::")
        res.append("    && v.ValidHistoryIdxStrict(i)")
        res.append(f"    && {self.module_name}.{self.name}(c.{self.hosts_field}[msg.Src()], v.History(i).{self.hosts_field}[msg.Src()], v.History(i+1).{self.hosts_field}[msg.Src()], msg)")
        res.append("  )")
        res.append("}")
        return "\n".join(res)

    def to_dafny_lemma(self):
        res = []
        res.append(f"lemma {self.get_lemma_name()}(c: Constants, v: Variables, v': Variables)")
        res.append("  requires v.WF(c)")
        res.append("  requires ValidMessages(c, v)")
        res.append(f"  requires {self.get_invariant_name()}(c, v)")
        res.append("  requires Next(c, v, v')")
        res.append(f"  ensures {self.get_invariant_name()}(c, v')")
        res.append("{")
        # Attempt proof
        res.append(f"  forall msg | msg in v'.network.sentMsgs && msg.{self.msg_cons}?")
        res.append("  ensures")
        res.append("  (exists i ::")
        res.append("    && v'.ValidHistoryIdxStrict(i)")
        res.append(f"    && {self.module_name}.{self.name}(c.{self.hosts_field}[msg.Src()], v'.History(i).{self.hosts_field}[msg.Src()], v'.History(i+1).{self.hosts_field}[msg.Src()], msg)")
        res.append("  ) {")
        res.append("    if msg !in v.network.sentMsgs {")
        res.append("      // witness and trigger")
        res.append("      var i := |v.history|-1;")
        res.append(f"      assert {self.module_name}.{self.name}(c.{self.hosts_field}[msg.Src()], v'.History(i).{self.hosts_field}[msg.Src()], v'.History(i+1).{self.hosts_field}[msg.Src()], msg);")
        res.append("    }")
        res.append("  }")
        res.append("}")
        return "\n".join(res)

    def __str__(self):
        return self.name + ": " + self.host_field + ", " + self.msg_cons


class Module:
    def __init__(self, raw: str, name="mod_name"):
        self.raw_string = raw
        self.name = name
        self.send_predicates = []
    
    def add_predicate(self, new_pred: SendPredicate):
        self.send_predicates.append(new_pred)

    def get_send_predicates(self):
        return self.send_predicates

    def __str__(self):
        res = []
        res.append("module " + self.name + ":")
        if len(self.send_predicates) == 0:
            res.append("   " + "no send predicates")
        
        for sp in self.send_predicates:
            res.append("   " + sp.__str__())
        res.append("")
        return "\n".join(res)


class MessageInvariantsFile:

    def __init__(self, modules: [Module]):
        self.modules = modules

    def to_dafny_string(self):
        res = []

        # Module preamble
        for inc in includes:
            res.append(f"include \"{inc}\"\n")
        res.append("module MessageInvariants {")
        for imp in imports:
            res.append(f"import opened {imp}")
        res.append("")

        # Define Send Invariants
        for module in self.modules:
            for send_predicate in module.get_send_predicates():
                res.append(send_predicate.to_dafny_invariant())
            res.append("")

        # Main invariant and obligations
        res.append("ghost predicate MessageInv(c: Constants, v: Variables)")
        res.append("{")
        res.append("  && v.WF(c)")
        res.append("  && ValidVariables(c, v)")
        for module in self.modules:
            for send_predicate in module.get_send_predicates():
                res.append(f"  && {send_predicate.get_invariant_name()}(c, v)")
        res.append("}")
        res.append("")
        
        res.append(commons["InitImpliesMessageInv"])
        res.append("")
        res.append(commons["MessageInvInductiveHeader"])
        res.append("{")
        res.append("  InvNextValidVariables(c, v, v');")
        for module in self.modules:
            for send_predicate in module.get_send_predicates():
                res.append(f"  {send_predicate.get_lemma_name()}(c, v, v');")
        res.append("}")
        res.append("")
        res.append("")

        res.append("/***************************************************************************************\n" +
                   "*                                     Aux Proofs                                       *\n" +
                   "***************************************************************************************/")
        res.append("")

        # Define lemmas
        for module in self.modules:
            for send_predicate in module.get_send_predicates():
                res.append(send_predicate.to_dafny_lemma())
            res.append("")
        res.append("} // end module MessageInvariants")
        return "\n".join(res)


