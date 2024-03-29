include "spec.dfy"

module OwnershipInvariants {
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

/***************************************************************************************
*                                   Definitions                                        *
***************************************************************************************/

  // Standard
  ghost predicate {:trigger KeyInFlightByMessage} UniqueKeyInFlight(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    exists msg :: msg in v.network.sentMsgs && KeyInFlightByMessage(c, v, msg, k)
  }

  // Disjunction for each host type
  ghost predicate {:trigger UniqueKeyInFlight} KeyInFlightByMessage(c: Constants, v: Variables, msg: Message, k: UniqueKey) 
    requires v.WF(c)
  {
    && msg in v.network.sentMsgs
    && ((0 <= msg.Dst() < |c.clients| &&
          ClientHost.UniqueKeyInFlightForHost(c.clients[msg.Dst()], v.Last().clients[msg.Dst()], k, msg)
        )
        || (0 <= msg.Dst() < |c.server| &&
            ServerHost.UniqueKeyInFlightForHost(c.server[msg.Dst()], v.Last().server[msg.Dst()], k, msg)
        )
    )
  }

  // One for each host type
  ghost predicate NoClientOwnsKey(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    forall idx | 0 <= idx < |c.clients| 
    :: 
    !ClientHost.HostOwnsUniqueKey(c.clients[idx], v.Last().clients[idx], k)
  }

  // One for each host type
  ghost predicate NoServerOwnsKey(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    forall idx | 0 <= idx < |c.server|
    :: 
    !ServerHost.HostOwnsUniqueKey(c.server[idx], v.Last().server[idx], k)
  }

  // Conjunction of corresponding assertions for each host type
  ghost predicate {:trigger KeyInFlightByMessage, UniqueKeyInFlight} 
  NoHostOwnsKey(c: Constants, v: Variables, k: UniqueKey) 
    requires v.WF(c)
  {
    && NoClientOwnsKey(c, v, k)
    && NoServerOwnsKey(c, v, k)
  }

/***************************************************************************************
*                                    Invariants                                        *
***************************************************************************************/

  // Standard
  ghost predicate AtMostOneInFlightMessagePerKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k, m1, m2 | KeyInFlightByMessage(c, v, m1, k) && KeyInFlightByMessage(c, v, m2, k)
    :: m1 == m2
  }

  // Standard
  ghost predicate {:trigger ServerHost.HostOwnsUniqueKey, ClientHost.HostOwnsUniqueKey} 
  HostOwnsKeyImpliesNotInFlight(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoHostOwnsKey(c, v, k)
    ::
    !UniqueKeyInFlight(c, v, k)
  }

  // One per host type
  ghost predicate AtMostOneOwnerPerKeyClients(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2, k | 
      && 0 <= h1 < |c.clients|
      && 0 <= h2 < |c.clients|
      && ClientHost.HostOwnsUniqueKey(c.clients[h1], v.Last().clients[h1], k) 
      && ClientHost.HostOwnsUniqueKey(c.clients[h2], v.Last().clients[h2], k) 
    ::
      && h1 == h2
  }

  // One per host type
  ghost predicate AtMostOneOwnerPerKeyServers(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall h1, h2, k | 
      && 0 <= h1 < |c.server|
      && 0 <= h2 < |c.server|
      && ServerHost.HostOwnsUniqueKey(c.server[h1], v.Last().server[h1], k) 
      && ServerHost.HostOwnsUniqueKey(c.server[h2], v.Last().server[h2], k) 
    ::
      && h1 == h2
  }

  // Only needed if more than one host type
  ghost predicate ClientsOwnKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoClientOwnsKey(c, v, k) :: NoServerOwnsKey(c, v, k)
  }

  // Only needed if more than one host type
  ghost predicate ServersOwnKey(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall k | !NoServerOwnsKey(c, v, k) :: NoClientOwnsKey(c, v, k)
  }

  ghost predicate OwnershipInv(c: Constants, v: Variables)
  {
    && v.WF(c)
    && AtMostOneInFlightMessagePerKey(c, v)
    && AtMostOneOwnerPerKeyClients(c, v)
    && AtMostOneOwnerPerKeyServers(c, v)
    && HostOwnsKeyImpliesNotInFlight(c, v)
    && ClientsOwnKey(c, v)   // Only needed if more than one host type
    && ServersOwnKey(c, v)   // Only needed if more than one host type
  }

  // Base obligation
  lemma InitImpliesOwnershipInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures OwnershipInv(c, v)
  {}

  // Inductive obligation
  lemma OwnershipInvInductive(c: Constants, v: Variables, v': Variables)
    requires OwnershipInv(c, v)
    requires Next(c, v, v')
    ensures OwnershipInv(c, v')
  {
    InvNextAtMostOneInFlightMessagePerKey(c, v, v');
    InvNextHostOwnsKeyImpliesNotInFlight(c, v, v');
    InvNextAtMostOwnerPerKeyClients(c, v, v');
    InvNextAtMostOwnerPerKeyServers(c, v, v');
    InvNextClientsOwnKey(c, v, v');
    InvNextServersOwnKey(c, v, v');
  }


/***************************************************************************************
*                                 InvNext Proofs                                       *
***************************************************************************************/


lemma InvNextAtMostOneInFlightMessagePerKey(c: Constants, v: Variables, v': Variables)
  requires v'.WF(c)
  requires OwnershipInv(c, v)
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
  requires OwnershipInv(c, v)
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
  requires OwnershipInv(c, v)
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
        var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
        assert dsStep.msgOps.recv.value == msg by {
          if dsStep.msgOps.recv.value != msg {
            var m' := dsStep.msgOps.recv.value;
            assert !KeyInFlightByMessage(c, v, m', k);
          }
        }
      } else {
        assert !(NoHostOwnsKey(c, v, k));
      }
    }
  }
}

lemma InvNextAtMostOwnerPerKeyClients(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneOwnerPerKeyClients(c, v')
{
  forall h1, h2, k | 
      && 0 <= h1 < |c.clients|
      && 0 <= h2 < |c.clients|
      && ClientHost.HostOwnsUniqueKey(c.clients[h1], v'.Last().clients[h1], k) 
      && ClientHost.HostOwnsUniqueKey(c.clients[h2], v'.Last().clients[h2], k) 
  ensures
     && h1 == h2
  {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    if h1 != h2 {
      assert KeyInFlightByMessage(c, v, dsStep.msgOps.recv.value, k);  
      assert UniqueKeyInFlight(c, v, k);
    }
  }
}

lemma InvNextAtMostOwnerPerKeyServers(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures AtMostOneOwnerPerKeyServers(c, v')
{}

lemma InvNextClientsOwnKey(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures ClientsOwnKey(c, v')
{
  forall k | !NoClientOwnsKey(c, v', k)
  ensures NoServerOwnsKey(c, v', k) {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    var idx :| 0 <= idx < |c.clients| && ClientHost.HostOwnsUniqueKey(c.clients[idx], v'.Last().clients[idx], k);
    if ClientHost.HostOwnsUniqueKey(c.clients[idx], v.Last().clients[idx], k) {
      assert !UniqueKeyInFlight(c, v, k);
    } else {
      assert UniqueKeyInFlight(c, v, k);
    }
  }
}

lemma InvNextServersOwnKey(c: Constants, v: Variables, v': Variables) 
  requires v'.WF(c)
  requires OwnershipInv(c, v)
  requires Next(c, v, v')
  ensures ServersOwnKey(c, v')
{
  forall k | !NoServerOwnsKey(c, v', k)
  ensures NoClientOwnsKey(c, v', k) {
    var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
    var idx :| 0 <= idx < |c.server| && ServerHost.HostOwnsUniqueKey(c.server[idx], v'.Last().server[idx], k);
    if ServerHost.HostOwnsUniqueKey(c.server[idx], v.Last().server[idx], k) {
      assert !UniqueKeyInFlight(c, v, k);
    } else {
      assert UniqueKeyInFlight(c, v, k);
    }
  }
}

} // end module ShardedKVProof