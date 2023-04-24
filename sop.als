sig Resource {}

sig Url {
  protocol: Protocol,
  host: Domain,
  port: lone Port,
  path: Path
}
sig Protocol, Port, Path {}
sig Domain { subsumes: set Domain }

one sig Dns {
  map: Domain -> Server
}

abstract sig Endpoint {}
abstract sig Client extends Endpoint {}
abstract sig Server extends Endpoint {
  resources: Path -> lone Resource
}

fact ServerAssumption {
  all s1, s2: Server | 
    (some Dns.map.s1 & Dns.map.s2) implies s1.resources = s2.resources
}

///check { 
 //   all r1, r2: HttpRequest | r1.url = r2.url implies r1.response = r2.response 
//} for 3 


