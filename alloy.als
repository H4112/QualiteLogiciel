open util/integer

let MAPSIZE = 10
let DNB = 3
let RNB = 4
let RCAP = 10
let DCAP = 10

fun abs[x: Int]: Int {
	x >= 0 => x else x.mul[-1]
}

fun distance[i1,i2: Intersection]: Int {
	abs[i1.x - i2.x] + abs[i1.y - i2.y]
}

sig Produit {}

sig Time {}

sig Intersection {
    x,y : Int
}

sig Drone {
    i: Intersection->Time,
    produits: Produit->Time,
    destination: Receptacle->Time
}

sig Receptacle {
    i: Intersection,
    produits: Produit->Time
}

sig Commande {
    produits: Produit->Time,
    adresse: Receptacle
}

one sig Entrepot extends Receptacle {}

fact Map { all i : Intersection | i.x >=0 && i.y >= 0 && i.x <= MAPSIZE && i.y <= MAPSIZE }

fact NbDrones { #Drone = DNB }

fact NbReceptacles { #Receptacle >= 2 && #Receptacle = RNB }

fact CapaciteDrone { all d: Drone, t: Time | #d.produits.t <= DCAP }

fact CapaciteReceptacle { all r: Receptacle, t: Time | #r.produits.t <= RCAP }

fact Chemin { all r: Receptacle, e: Entrepot | some s: set Receptacle | r in s && e in s && all r1,r2: s | distance[r1.i, r2.i] <= 3 }

pred init[t: Time] {
	no Drone.produits.t
    no Commande
    one e: Entrepot | all r:Receptacle | r = e || no r.produits.t
    one e: Entrepot | all d: Drone | e.i = d.i
    no Drone.destination.t
}

pred Simulation {
	init[first]
    all t: Time - last | let t' = t.next | -- between each timestep
    all d: Drone
    move[t,t',d]
}

run Simulation for exactly 3 Drone, 2 Receptacle

