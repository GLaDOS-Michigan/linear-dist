namespace Microsoft.Dafny
{

  public class SendInvariant {

    public string functionName;  // name of the send predicate
    public string msgType;  // name of the type of message concerning this predicate
    public string module;   // name of the module this function belongs
    public string variableField;  // which field in distributedSystem.Hosts?
  }
}