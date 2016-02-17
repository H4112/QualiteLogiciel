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

sig Intersection {
    x,y : Int
}

sig Drone {
    i: Intersection,
    produits: some Produit,
    destination: Receptacle
}

sig Receptacle {
    i: Intersection,
    produits: set Produit
}

sig Commande {
    produits: some Produit,
    adresse: Receptacle
}

sig Entrepot extends Receptacle {}

fact Map { all i : Intersection | i.x >=0 && i.y >= 0 && i.x <= MAPSIZE && i.y <= MAPSIZE }

fact NbDrones { #Drone = DNB }

fact NbReceptacles { #Receptacle >= 2 && #Receptacle = RNB }

fact UnEntrepot { #Entrepot = 1 }

fact CapaciteDrone { all d: Drone | #d.produits <= DCAP }

fact CapaciteReceptacle { all r: Receptacle | #r.produits <= RCAP }

fact Chemin { all r: Receptacle, e: Entrepot | some s: set Receptacle | r in s && e in s && all r1,r2: s | distance[r1.i, r2.i] <= 3 }

assert Different { all r1,r2: Receptacle | r1.i != r2.i }

check Different


