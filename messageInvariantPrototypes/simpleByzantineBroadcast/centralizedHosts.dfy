include "types.dfy"


/***************************************************************************************
*                                      Leader Host                                     *
***************************************************************************************/

module Host {
  import opened UtilitiesLibrary
  import opened Types

  datatype Constants = Constants(id: HostId, f: nat, broadcastValue: Option<Value>, isByz: bool) 
  {

    ghost predicate ConstantsValidForHost(id: HostId, f: nat) {
      && this.id == id
      && this.f == f
    }


    ghost predicate IsBroadcaster() {
      broadcastValue.Some?
    }
  } // end datatype Constants

  datatype Variables = Variables(
    echoValue: Option<Value>,
    receivedEchosForValue: map<Value, set<HostId>>,
    decided: Option<Value> ) 
  {
  } // end datatype Variables (Leader)

  ghost function GetFaultyNodes(grp_c: seq<Constants>) : (res: set<HostId>)
    ensures forall x:nat :: x in res <==> x < |grp_c| && grp_c[x].isByz

  ghost predicate GroupWFConstants(grp_c: seq<Constants>, f: nat) {
    && 0 < f
    && |grp_c| == 3*f + 1
    && |GetFaultyNodes(grp_c)| == f  // f faulty nodes
    && (forall idx: nat | idx < |grp_c| && grp_c[idx].broadcastValue.Some?  // only first node is broadcaster
        :: idx == 0
    )
    && (forall idx: nat | idx < |grp_c|
        :: grp_c[idx].ConstantsValidForHost(idx, f))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) {
    && 0 < f
    && GroupWFConstants(grp_c, f)
    && |grp_v| == |grp_c|
  }

  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>, f: nat) 
    requires GroupWF(grp_c, grp_v, f)
  {
    forall i | 0 <= i < |grp_c| :: Init(grp_c[i], grp_v[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.echoValue.None?
    && v.receivedEchosForValue == map[]
    && v.decided == None
  }

  // receiver for a byzantine sender gets a random label with correct src, but unspecifield payload.
  datatype TransitionLabel =
    | BroadcastLbl(src: HostId, value: Value)
    | RecvBroadcastLbl(src: HostId, value: Value)
    | EchoLbl(src: HostId, value: Value) 
    | RecvEchoLbl(src: HostId, value: Value) 
    | InternalLbl(src: HostId)

  datatype Step =
    BroadcastStep() | RecvBroadcastStep() | EchoStep() | RecvEchoStep() | ByzantineStep() | StutterStep()

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, lbl: TransitionLabel)
  {
    match step
      case BroadcastStep => NextBroadcastStep(c, v, v', lbl)
      case RecvBroadcastStep => NextRecvBroadcastStep(c, v, v', lbl)
      case EchoStep => NextEchoStep(c, v, v', lbl)
      case RecvEchoStep => NextRecvEchoStep(c, v, v', lbl)
      case ByzantineStep => NextByzantineStep(c, v, v', lbl)
      case StutterStep => NextStutterStep(c, v, v', lbl)
  }

  ghost predicate NextBroadcastStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.BroadcastLbl?
    && lbl.src == c.id
    && c.broadcastValue.Some?
    && lbl.value == c.broadcastValue.value
    && v' == v
  }

  ghost predicate NextRecvBroadcastStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.RecvBroadcastLbl?
    && lbl.src == 0       // can only receive from designated broadcaster
    && v.echoValue.None?  // can only receive one value ever
    && v' == v.(
      echoValue := Some(lbl.value)
    )
  }

  ghost predicate NextEchoStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.EchoLbl?
    && lbl.src == c.id
    && v.echoValue.Some?
    && lbl.value == v.echoValue.value
    && v' == v
  }

  ghost function UpdateReceivedEchosForValue(receivedEchosForValue: map<Value, set<HostId>>, value: Value, host: HostId) : map<Value, set<HostId>>{
    receivedEchosForValue[value := if value in receivedEchosForValue then receivedEchosForValue[value] + {host} else  {host}]
  }

  ghost predicate NextRecvEchoStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.RecvEchoLbl?
    && (forall x | x in v.receivedEchosForValue :: lbl.src !in v.receivedEchosForValue[x]) // can't have received echo from this source
    && v' == v.(
      receivedEchosForValue := UpdateReceivedEchosForValue(v.receivedEchosForValue, lbl.value, lbl.src)
    )
  }

  ghost predicate NextDecideStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel, decisionValue: Value) {
    && lbl.InternalLbl?
    && v.decided.None?
    && decisionValue in v.receivedEchosForValue
    && |v.receivedEchosForValue[decisionValue]| >= 2*c.f+1
    && v' == v.(decided := Some(decisionValue))
  }

  ghost predicate NextStutterStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && lbl.InternalLbl?
    && v' == v
  }
  
  ghost predicate NextByzantineStep(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel) {
    && c.isByz
    && lbl.InternalLbl?
    && lbl.src == c.id  // src is authenticated, and cannot be faked
    && v' == v'         // undefined behavior
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, lbl: TransitionLabel)
  {
    exists step :: NextStep(c, v, v', step, lbl)
  }
}  // end module LeaderHost