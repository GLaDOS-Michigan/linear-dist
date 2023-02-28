# Spec

Single machine state machine (IronFleet style)


# Protocol (simplified host, state machine combining hosts)

def Host(ghost linear net):
  ghost linear lock, net := receive(net)
  self.have_lock := true;
  // Do stuff
  ghost linear net := send(I HAVE THE LOCK, HAHAHA);
  self.have_lock := false;
  ghost linear net := send(lock);
  return net


# Implementation (optimizations, machine integers, etc.)

fn Host(&mut net_client)
  ensures self == old(self).Host(net_client.history)

  bool b := net_client.receive();
  self.have_lock := true;

  // Do optimized stuff
  
  self.have_lock := false;
  net_client.send(lock);
  
  str = "I HAVE"
  str += "THE LOCK" + "HA" * 3;
  net_client.send(str);

}

# Threaded Implementation 
fn HostThread(shared net_lock)
    let net = net_lock.acquire();
    let b := net.receive();


