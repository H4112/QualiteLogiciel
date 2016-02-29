//permet de faire des sommes, des produits...
open util/integer
//permet d'utiliser time.next pour se déplacer dans le temps
open util/ordering[Time] as to

//constantes de l'énoncé, fixées arbitrairement
let MAPSIZE = 10
let DNB = 3
let RNB = 3
let RCAP = 10
let DCAP = 10

//calcule la valeur absolue d'un nombre
fun abs[x: Int]: Int {
	x >= 0 => x else x.mul[-1]
}

//calcule la distance de Manhattan entre deux Intersection :
//|x1-x2| + |y1-y2|
fun distance[i1,i2: Intersection]: Int {
	abs[i1.x - i2.x].add[abs[i1.y - i2.y]]
}

//produits transportés par les drones
sig Produit {}

//représente les différents instants du programme
sig Time {}

//position sur le plan
sig Intersection {
    x,y : Int
}

//drone transportant des produits
sig Drone {
    i: Intersection->Time,
    produits: Produit->Time,
    destination: Receptacle->Time
}

//destination possible pour les produits
sig Receptacle {
    i: Intersection,
    produits: Produit->Time
}

//commande possédant des produits à livrer à l'adresse indiquée
sig Commande {
    produits: Produit->Time,
    adresse: Receptacle
}

//entrepôt où se trouvent les produits à l'instant t0
one sig Entrepot extends Receptacle {}

//limites du plan : toutes les intersections se trouvent à x et y entre 0 et MAPSIZE
fact Map { all i : Intersection | i.x >= 0 && i.y >= 0 && i.x <= MAPSIZE && i.y <= MAPSIZE }

//nombre de drones connu
fact NbDrones { #Drone = DNB }

//nombre de réceptacles connu
fact NbReceptacles { #Receptacle >= 2 && #Receptacle = RNB }

//deux intersections ne partagent pas la même position
fact IntersectionsSeparees { all i1, i2: Intersection | i1 = i2 || i1.x != i2.x && i1.y != i2.y }

//deux réceptacles ne sont pas à la même position
fact ReceptaclesSepares { all r1, r2: Receptacle | r1 = r2 || r1.i != r2.i }

//les drones ne peuvent porter plus de DCAP produits
fact CapaciteDrone { all d: Drone, t: Time | #d.produits.t <= DCAP }

//les réceptacles ne peuvent contenir plus de RCAP produits
//et si plus de RCAP produits doivent être livrés à ce réceptacle ? On le vide pas de temps à autre ?
fact CapaciteReceptacle { all r: Receptacle, t: Time | #r.produits.t <= RCAP }

//"liste chaînée" de réceptacles permettant de relier 2 réceptacles
sig Chain {
	that : one Receptacle,
	nextc : lone Chain
}

//deux Chain différents font référence à des éléments différents
//ça va poser problème
fact UniqueChain {
	all a,b: Chain | a = b
		|| a.that != b.that || a.nextc != b.nextc
}

//chaque point doit être séparé du précédent par 3 au max
fact ChainMaxDist {
	all c: Chain | distance[c.that.i, c.nextc.that.i] <= 3
}

//il existe toujours une suite de réceptacles (chemin) entre l'entrepôt et n'importe quel réceptacle,
//où chaque réceptacle de cette suite est séparé du précédent par une distance d'au plus 3
fact CheminExiste {
	all e: Entrepot, r: Receptacle |
		e = r || Chemin[e, r]
}

pred Chemin[depr, arrr: Receptacle] {
	one dep, arr: Chain | dep.that = depr && arr.that = arrr &&
	no arr.nextc && //fin de la chaîne : pointe sur rien
	arr in dep.*nextc &&  //on atteint l'arrivée en partant du départ
	(all c: Chain | c.that not in c.nextc.*nextc.that) //on n'a aucune boucle
}

//initialisation : pas de produits dans les drones, pas de produits dans les réceptacles,
//tous les produits et drones sont à l'entrepôt.
//et.... pas de commande ? Mais alors elles apparaissent comment et où ?
pred init[t: Time] {
	no Drone.produits.t
    no Commande
	//soit r est l'entrepôt, soit c'est un réceptacle et donc pas de produit.
    one e: Entrepot | all r:Receptacle | r = e || no r.produits.t 
    one e: Entrepot | all d: Drone | e.i = d.i.t
    no Drone.destination.t
}

pred Simulation {
	init[first]
    all t: Time - last | let t' = t.next | -- between each timestep
    all d: Drone |
    move[t,t',d]
}

pred move[t, t': Time, d: Drone] {
	1=1
}


run Simulation for exactly 3 Drone, 5 Receptacle, 
							 1 Time, 5 Produit, 10 Intersection, 3 Commande, 4 Chain, 6 Int
// attention à ne pas contredire les faits NbDrones et NbReceptacles !
