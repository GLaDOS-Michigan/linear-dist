include "messageInvariants.dfy"

module LockServerProof {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations
  import opened MessageInvariants

/***************************************************************************************
*                                   Definitions                                        *
***************************************************************************************/

  ghost predicate UniqueKeyInFlight(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    exists msg :: KeyInFlightByMessage(c, v, msg, k)
  }

  ghost predicate KeyInFlightByMessage(c: Constants, v: Variables, msg: Message, k: UniqueKey) 
    requires v.WF(c)
  {
    && msg in v.network.sentMsgs
    && ((0 <= msg.Dst() < |c.clients| &&
          ClientHost.UniqueKeyInFlightForHost(c.clients[msg.Dst()], v.clients[msg.Dst()], k, msg)
        )
        || (0 <= msg.Dst() < |c.server| &&
            ServerHost.UniqueKeyInFlightForHost(c.server[msg.Dst()], v.server[msg.Dst()], k, msg)
        )
    )
  }

  ghost predicate NoClientOwnsKey(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    forall idx | 0 <= idx < |c.clients| 
    :: 
    !ClientHost.HostOwnsUniqueKey(c.clients[idx], v.clients[idx], k)
  }

  ghost predicate NoServerOwnsKey(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    forall idx | 0 <= idx < |c.server|
    :: 
    !ServerHost.HostOwnsUniqueKey(c.server[idx], v.server[idx], k)
  }

  ghost predicate NoHostOwnsKey(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    && NoClientOwnsKey(c, v, k)
    && NoServerOwnsKey(c, v, k)
  }

/***************************************************************************************
*                                    Invariants                                        *
***************************************************************************************/


  ghost predicate AtMostOneInFlightMessagePerKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k, m1, m2 | KeyInFlightByMessage(c, v, m1, k) && KeyInFlightByMessage(c, v, m2, k)
    :: m1 == m2
  }

  ghost predicate HostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoHostOwnsKey(c, v, k)
    ::
    !UniqueKeyInFlight(c, v, k)
  }

  ghost predicate AtMostOneOwnerPerKeyClients(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2, k | 
      && 0 <= h1 < |c.clients|
      && 0 <= h2 < |c.clients|
      && ClientHost.HostOwnsUniqueKey(c.clients[h1], v.clients[h1], k) 
      && ClientHost.HostOwnsUniqueKey(c.clients[h2], v.clients[h2], k) 
    ::
      && h1 == h2
  }

  ghost predicate AtMostOneOwnerPerKeyServers(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2, k | 
      && 0 <= h1 < |c.server|
      && 0 <= h2 < |c.server|
      && ServerHost.HostOwnsUniqueKey(c.server[h1], v.server[h1], k) 
      && ServerHost.HostOwnsUniqueKey(c.server[h2], v.server[h2], k) 
    ::
      && h1 == h2
  }

  ghost predicate ClientsOwnKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoClientOwnsKey(c, v, k) :: NoServerOwnsKey(c, v, k)
  }

  ghost predicate ServersOwnKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoServerOwnsKey(c, v, k) :: NoClientOwnsKey(c, v, k)
  }

  ghost predicate ServerOwnsLockImpliesNoClientsOwnsLock(c: Constants, v: Variables)
  requires v.WF(c)
  {
    v.server[0].hasLock ==> 
    (forall id | c.ValidClientIdx(id) :: !v.clients[id].hasLock)
  }
  
  ghost predicate ApplicationInv(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && AtMostOneInFlightMessagePerKey(c, v)
    && AtMostOneOwnerPerKeyClients(c, v)
    && AtMostOneOwnerPerKeyServers(c, v)
    && HostOwnsKeyImpliesNotInFlight(c, v)
    && ServerOwnsLockImpliesNoClientsOwnsLock(c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && MessageInv(c, v)
    && ApplicationInv(c, v)
    && Safety(c, v)
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  {}

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
    InitImpliesMessageInv(c, v);
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    MessageInvInductive(c, v, v');
    InvNextAtMostOneInFlightMessagePerKey(c, v, v');
    InvNextHostOwnsKeyImpliesNotInFlight(c, v, v');
    InvNextAtMostOwnerPerKeyClients(c, v, v');
    InvNextAtMostOwnerPerKeyServers(c, v, v');
    InvNextServersOwnKey(c, v, v');
    AtMostOwnerPerKeyImpliesSafety(c, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/

lemma AtMostOwnerPerKeyImpliesSafety(c: Constants, v: Variables)
  requires v.WF(c)
  requires AtMostOneOwnerPerKeyClients(c, v)
  ensures Safety(c, v)
{
  forall idx1, idx2 | 
    && c.ValidClientIdx(idx1) 
    && c.ValidClientIdx(idx2) 
    && HoldsLock(c, v, idx1)
    && HoldsLock(c, v, idx2)
  ensures
   idx1 == idx2
  {
    // triggers
    assert ClientHost.HostOwnsUniqueKey(c.clients[idx1], v.clients[idx1], 0);
    assert ClientHost.HostOwnsUniqueKey(c.clients[idx2], v.clients[idx2], 0);
  }
}

lemma InvNextAtMostOneInFlightMessagePerKey(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneInFlightMessagePerKey(c, v')
{
  forall k, m1, m2 | KeyInFlightByMessage(c, v', m1, k) && KeyInFlightByMessage(c, v', m2, k) 
  ensures m1 == m2
  {
    if m1 != m2 {
      if KeyInFlightByMessage(c, v, m1, k) {
        InvNextAtMostOneInFlightHelper(c, v, v', m1, m2, k);
      } else {
        InvNextAtMostOneInFlightHelper(c, v, v', m2, m1, k);
      }
    }
  }
}

lemma InvNextAtMostOneInFlightHelper(c: Constants, v: Variables, v': Variables, m1: Message, m2: Message, k: UniqueKey)
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  // input constraints
  requires m1 != m2
  requires KeyInFlightByMessage(c, v, m1, k)
  requires !KeyInFlightByMessage(c, v, m2, k)
  // postcondition
  ensures !KeyInFlightByMessage(c, v', m2, k)
{
  assert UniqueKeyInFlight(c, v, k);
}

lemma InvNextHostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures HostOwnsKeyImpliesNotInFlight(c, v')
{
  forall k | !NoHostOwnsKey(c, v', k)
  ensures !UniqueKeyInFlight(c, v', k)
  {
    if UniqueKeyInFlight(c, v', k) {
      var msg :| KeyInFlightByMessage(c, v', msg , k);
      if msg in v.network.sentMsgs {
        assert KeyInFlightByMessage(c, v, msg, k);
        assert NoHostOwnsKey(c, v, k);  
        var dsStep :| NextStep(c, v, v', dsStep);
        assert dsStep.msgOps.recv.value == msg by {
          if dsStep.msgOps.recv.value != msg {
            var m' := dsStep.msgOps.recv.value;
            assert !KeyInFlightByMessage(c, v, m', k);
          }
        }
      } else {
        assert !(NoServerOwnsKey(c, v, k) && NoClientOwnsKey(c, v, k));
      }
    }
  }
}

lemma InvNextAtMostOwnerPerKeyClients(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneOwnerPerKeyClients(c, v')
{
  forall h1, h2, k | 
      && 0 <= h1 < |c.clients|
      && 0 <= h2 < |c.clients|
      && ClientHost.HostOwnsUniqueKey(c.clients[h1], v'.clients[h1], k) 
      && ClientHost.HostOwnsUniqueKey(c.clients[h2], v'.clients[h2], k) 
  ensures
     && h1 == h2
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if h1 != h2 {
      if ClientHost.HostOwnsUniqueKey(c.clients[h2], v'.clients[h2], k) {
        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);  
        assert UniqueKeyInFlight(c, v, k);
        assert false;
      }
      if ClientHost.HostOwnsUniqueKey(c.clients[h1], v'.clients[h1], k) {
        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);  
        assert UniqueKeyInFlight(c, v, k);
        assert false;
      }
    } 
  }
}

lemma InvNextAtMostOwnerPerKeyServers(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneOwnerPerKeyServers(c, v')
{
  forall h1, h2, k | 
      && 0 <= h1 < |c.server|
      && 0 <= h2 < |c.server|
      && ServerHost.HostOwnsUniqueKey(c.server[h1], v'.server[h1], k) 
      && ServerHost.HostOwnsUniqueKey(c.server[h2], v'.server[h2], k) 
  ensures
     && h1 == h2
  {
    var dsStep :| NextStep(c, v, v', dsStep);
    if h1 != h2 {
      if ServerHost.HostOwnsUniqueKey(c.server[h2], v'.server[h2], k) {
        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);  
        assert UniqueKeyInFlight(c, v, k);
        assert false;
      }
      if ServerHost.HostOwnsUniqueKey(c.server[h1], v'.server[h1], k) {
        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);  
        assert UniqueKeyInFlight(c, v, k);
        assert false;
      }
    }
  }
}

lemma InvNextClientsOwnKey(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ClientsOwnKey(c, v')
{
  forall k | !NoClientOwnsKey(c, v', k)
  ensures NoServerOwnsKey(c, v', k) {
    var dsStep :| NextStep(c, v, v', dsStep);
    var idx :| 0 <= idx < |c.clients| && ClientHost.HostOwnsUniqueKey(c.clients[idx], v'.clients[idx], k);
    if ClientHost.HostOwnsUniqueKey(c.clients[idx], v.clients[idx], k) {
      assert !UniqueKeyInFlight(c, v, k);
      if !NoServerOwnsKey(c, v', k) {
        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);
        assert false;
      }
    } else {
      assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);
      assert UniqueKeyInFlight(c, v, k);
    }
  }
}

lemma InvNextServersOwnKey(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures ServerOwnsLockImpliesNoClientsOwnsLock(c, v')
{
  forall k | !NoServerOwnsKey(c, v', k)
  ensures NoClientOwnsKey(c, v', k) {
    var dsStep :| NextStep(c, v, v', dsStep);
    var idx :| 0 <= idx < |c.server| && ServerHost.HostOwnsUniqueKey(c.server[idx], v'.server[idx], k);
    if ServerHost.HostOwnsUniqueKey(c.server[idx], v.server[idx], k) {
      assert !UniqueKeyInFlight(c, v, k);
      if !NoClientOwnsKey(c, v', k) {
        assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);
        assert false;
      }
    } else {
      assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);
      assert UniqueKeyInFlight(c, v, k);
    }
  }
}

} // end module LockServerProof