include "../../lib/UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  datatype Vote = Yes | No

  datatype Decision = Commit | Abort
}
