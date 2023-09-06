include "hosts.dfy"

module LeaderHostMono {
  import opened LeaderHost

  datatype VariablesHistory = VariablesHistory(h: seq<Variables>)

  

}