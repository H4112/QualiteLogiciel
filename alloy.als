//permet de faire des sommes, des produits...
open util/integer
open util/boolean
//permet d'utiliser time.next pour se déplacer dans le temps
open util/ordering[Time] as to

//constantes de l'énoncé, fixées arbitrairement
let MAPSIZE = 2
let DNB = 1
let RNB = 3
let RCAP = 7
let DCAP = 7

//calcule la valeur absolue d'un nombre
fun abs[x: Int]: Int {
	x >= 0 => x else x.mul[-1]
}

//calcule la distance de Manhattan entre deux Intersection :
//|x1-x2| + |y1-y2|
fun distance[i1,i2: Intersection]: Int {
	abs[i1.x.sub[i2.x]].add[abs[i1.y.sub[i2.y]]]
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
	i: Intersection one->Time,
	produits: Produit->Time,
	destination: Receptacle one->Time,
	chemin: Chain one->Time
}

//destination possible pour les produits
sig Receptacle {
	i: Intersection,
	produits: Produit->Time
}


//commande possédant des produits à livrer à l'adresse indiquée
sig Commande {
	produits: Produit->Time,
	adresse: one Receptacle
}

//entrepôt où se trouvent les produits à l'instant t0
one sig Entrepot extends Receptacle {}

fact NoCommandeEntrepot {
	no c: Commande | some e: Entrepot | c.adresse = e
}

//limites du plan : toutes les intersections se trouvent à x et y entre 0 et MAPSIZE
fact Map { all i : Intersection | i.x >= 0 && i.y >= 0 && i.x < MAPSIZE && i.y < MAPSIZE }

//nombre de drones connu
fact NbDrones { #Drone = DNB }

//nombre de réceptacles connu
fact NbReceptacles { #Receptacle = RNB }

//deux intersections ne partagent pas la même position
fact IntersectionsSeparees { all disj i1, i2: Intersection | i1.x != i2.x || i1.y != i2.y }

//deux réceptacles ne sont pas à la même position
fact ReceptaclesSepares { all disj r1, r2: Receptacle | r1.i != r2.i }

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
	all disj a,b: Chain | a.that != b.that && a.nextc != b.nextc
}

//chaque point doit être séparé du précédent par 3 au max
fact ChainMaxDist {
	all c: Chain | one c.nextc => distance[c.that.i, c.nextc.that.i] <= 3
}

//il existe toujours une suite de réceptacles (chemin) entre l'entrepôt et n'importe quel réceptacle,
//où chaque réceptacle de cette suite est séparé du précédent par une distance d'au plus 3
fact CheminExiste {
	one e: Entrepot | all r: Receptacle | some _: Chain |
		e != r => Chemin[e, r, _]
}

pred Chemin[depr, arrr: Receptacle, chemin: Chain] {
	one arr: Chain | {
		chemin.that = depr
		arr.that = arrr
		no arr.nextc //fin de l^a chaîne : pointe sur rien
		arr in chemin.^nextc //on atteint l'arrivée en partant du départ
		(all c: chemin.*nextc | c.that not in c.^nextc.that) //on n'a aucune boucle
	}
}


//initialisation : pas de produits dans les drones, pas de produits dans les réceptacles,
//tous les produits et drones sont à l'entrepôt.
//et.... pas de commande ? Mais alors elles apparaissent comment et où ?
pred init[t: Time] {
	no Drone.produits.t
	all c: Commande | #c.produits.t > 0
	//soit r est l'entrepôt, soit c'est un réceptacle et donc pas de produit.
	one e: Entrepot | {
		all r: Receptacle | r = e || no r.produits.t 
		all d: Drone | d.i.t = e.i && d.destination.t = e && no d.chemin.t
		all p: Produit | p in e.produits.t
	}
	// un produit ne peut être dans plusieurs commandes
	all p: Produit | lone c: Commande | p in c.produits.t
}

pred Simulation {
	init[first]
	all t: Time - last | let t' = t.next | -- between each timestep
	{
		all d: Drone | majDrone[t,t',d]
		// màj produits entrepot
		all p: Produit | one e: Entrepot | (p in e.produits.t && (no d: Drone | p in d.produits.t')) => p in e.produits.t'
		// màj produits des commandes
		all c: Commande | #c.produits.t' != 0 => c.produits.t' = c.produits.t
		// màj produits des réceptacles
		all r: Receptacle | (no d: Drone | d.destination.t = r && d.i.t = r.i) => r.produits.t' = r.produits.t
	}
}

pred majDrone[t, t': Time, d: Drone] {
	one e: Entrepot | 
	d.i.t = d.destination.t.i => { // drone à destination
		d.i.t = e.i => { //on prend une commande
			one c: {c: Commande | #c.produits.t > 0} | {
				#c.produits.t' = 0
				d.produits.t' = c.produits.t
				c.produits.t not in e.produits.t'
				d.destination.t' = c.adresse
				//Chemin[e, c.adresse, d.chemin.t']
			}
		} else {//on livre
			#d.produits.t' = 0
			d.destination.t.produits.t' = (d.destination.t.produits.t + d.produits.t)
			d.destination.t' = e
			Chemin[d.destination.t, e, d.chemin.t']
		}
		d.i.t' = d.i.t
	} else { // drone en chemin
		d.i.t = d.chemin.t.that.i => d.chemin.t' = d.chemin.t.nextc //on cherche la prochaine destination
		else d.chemin.t' = d.chemin.t
		d.destination.t' = d.destination.t
		d.produits.t' = d.produits.t
		avancer[t, t', d]
	}
}

//avancer le drone d'un pas en x et si les x sont déjà alignés,
//avancer d'un pas en y
pred avancer[t, t': Time, d: Drone] {
	d.i.t.x = d.chemin.t'.that.i.x => {
		d.i.t'.x = d.i.t.x
		d.i.t.y < d.chemin.t'.that.i.y => d.i.t'.y = d.i.t.y.add[1]
		else d.i.t'.y = d.i.t.y.sub[1]
	} else {
		d.i.t'.y = d.i.t.y
		d.i.t.x < d.chemin.t'.that.i.x => d.i.t'.x = d.i.t.x.add[1]
		else d.i.t'.x = d.i.t.x.sub[1]
	}
}

run Simulation for exactly 1 Drone, 3 Receptacle, 
							 1 Time, 1 Produit, 10 Intersection, exactly 1 Commande, 10 Chain, 4 Int
// attention à ne pas contredire les faits NbDrones et NbReceptacles !
