include "types.dfy"

module Network {
import opened Types

datatype EnvStep = 
    IoStep(actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)

datatype Environment = Env(
        sentPackets:set<Packet>,
        nextStep:EnvStep
    )

predicate EnvironmentInit(e:Environment) {
    e.sentPackets == {}
}

predicate ValidIoStep(iostep:EnvStep) 
    requires iostep.IoStep?
{
    && (forall r | r in iostep.recvIos :: r.dst == iostep.actor)
    && (forall s | s in iostep.sendIos :: s.src == iostep.actor)
}


predicate EnvironmentNext(e:Environment, e':Environment)
{
    match e.nextStep {
        case IoStep(actor, recvIos, sendIos) => 
            && ValidIoStep(e.nextStep)
            && e'.sentPackets == e.sentPackets + (set s | s in sendIos)
            && (forall r | r in recvIos :: r in e.sentPackets)
    }
}

}