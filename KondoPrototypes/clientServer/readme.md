# Readme

This is the "client_server_ae" protocol from [DuoAI](https://github.com/VeriGu/DuoAI/tree/master/protocols) (OSDI'22).

Multiple clients can send requests to a server. The server processes each request and returns a response to the respective client. Clients send requests asynchronously, and the server may process the requests out-of-order.
Safety condition is that every client only gets responses for their own requests, marked by their unique identifier.

Note that compared to "client_server_ae", server receives requests and send response in separate steps, rather than one atomic step. This is to add some degree of complexity to the protocol and proof.
