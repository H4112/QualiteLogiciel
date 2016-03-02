//permet de faire des sommes, des produits...
open util/integer
//permet d'utiliser time.next pour se déplacer dans le temps
open util/ordering[Time] as to

//constantes de l'énoncé, fixées arbitrairement
// taille de la carte (0..MAPSIZE-1)^2
let MAPSIZE = 2
// nb de drones
//let DNB = 2
// nb de réceptacles
//let RNB = 3
// capacité des réceptacles
let RCAP = 7
// capacité des drones
let DCAP = 7
// capacité de la batterie
let BCAP = 3

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
	chemin: Chain one->Time,
	batterie: Int one->Time
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


//aucune commande dont l'adresse est l'entrepot
fact NoCommandeEntrepot {
	no c: Commande | some e: Entrepot | c.adresse = e
}

//limites du plan : toutes les intersections se trouvent à x et y entre 0 et MAPSIZE
fact Map { all i : Intersection | i.x >= 0 && i.y >= 0 && i.x < MAPSIZE && i.y < MAPSIZE }

//nombre de drones connu
//fact NbDrones { #Drone = DNB }

//nombre de réceptacles connu
//fact NbReceptacles { #Receptacle = RNB }

//deux intersections ne partagent pas la même position
fact IntersectionsSeparees { all disj i1, i2: Intersection | i1.x != i2.x || i1.y != i2.y }

//deux réceptacles ne sont pas à la même position
fact ReceptaclesSepares { all disj r1, r2: Receptacle | r1.i != r2.i }

//les drones ne peuvent porter plus de DCAP produits
fact CapaciteDrone { all d: Drone, t: Time | #d.produits.t <= DCAP }

//les réceptacles ne peuvent contenir plus de RCAP produits
//et si plus de RCAP produits doivent être livrés à ce réceptacle ? On le vide pas de temps à autre ?
fact CapaciteReceptacle { all r: Receptacle, t: Time | #r.produits.t <= RCAP }

//la batterie d'un drone est toujours entre 0 et BCAP inclus
//fact CapaciteBatterie { all d: Drone, t: Time | d.batterie.t >= 0 && d.batterie.t <= BCAP }

/***** CHEMIN ****/

//"liste chaînée" de réceptacles permettant de relier 2 réceptacles
sig Chain {
	that : one Receptacle,
	nextc : lone Chain
}

//deux Chain différents font référence à des éléments différents
fact UniqueChain {
	all disj a,b: Chain | a.that != b.that || a.nextc != b.nextc
}

//chaque point doit être séparé du précédent par BCAP au max
fact DistanceEntreReceptacles {
	all c: Chain | one c.nextc => distance[c.that.i, c.nextc.that.i] <= BCAP
}

//il existe toujours une suite de réceptacles (chemin) entre l'entrepôt et n'importe quel réceptacle,
//où chaque réceptacle de cette suite est séparé du précédent par une distance d'au plus BCAP
fact CheminExiste {
	one e: Entrepot | all r: Receptacle |
		e != r => (some _: Chain | Chemin[e, r, _])
}

fact PasDeBoucle {
	all c: Chain | c.that not in c.^nextc.that
}

pred Chemin[depr, arrr: Receptacle, chemin: Chain] {
	one arr: Chain | {
		chemin.that = depr
		arr.that = arrr
		no arr.nextc //fin de la chaîne : pointe sur rien
		arr in chemin.*nextc //on atteint l'arrivée en partant du départ
		//(all c: (chemin.*nextc + chemin) | c.that not in c.*nextc.that) //on n'a aucun cycle
	}
}

/***** Simulation *****/

//initialisation : pas de produits dans les drones, pas de produits dans les réceptacles,
//tous les produits et drones sont à l'entrepôt.
//et.... pas de commande ? Mais alors elles apparaissent comment et où ?
pred init[t: Time] {
	no Drone.produits.t
	all c: Commande | #c.produits.t > 0
	//soit r est l'entrepôt, soit c'est un réceptacle et donc pas de produit.
	one e: Entrepot | {
		all r: Receptacle | r = e || (no r.produits.t && distance[e.i,r.i] = 2)
		all d: Drone | {
			d.i.t = e.i
			d.destination.t = e
			d.chemin.t.that = e
			d.batterie.t = BCAP
		}
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
		all p: Produit | one e: Entrepot | (p in e.produits.t && (no d: Drone | p in d.produits.t')) => p in e.produits.t' else p not in e.produits.t'
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
			(no c: Commande | #c.produits.t > 0 && no d': Drone | d != d' && c.produits.t in d'.produits.t') => {
				d.produits.t' = d.produits.t
				d.destination.t' = d.destination.t
				d.chemin.t' = d.chemin.t
				d.batterie.t' = d.batterie.t
				d.i.t' = d.i.t
			}
			else one c: {c: Commande | #c.produits.t > 0 && no d': Drone | d != d' && c.produits.t in d'.produits.t'} | {
				#c.produits.t' = 0
				d.produits.t' = c.produits.t
				c.produits.t not in e.produits.t'
				d.destination.t' = c.adresse
				Chemin[e, c.adresse, d.chemin.t']
			}
		} else {//on livre
			#d.produits.t' = 0
			d.destination.t.produits.t' = (d.destination.t.produits.t + d.produits.t)
			d.destination.t' = e
			Chemin[d.destination.t, e, d.chemin.t']
		}
		d.i.t' = d.i.t
		d.batterie.t' = d.batterie.t
	} else { // drone en chemin
		(d.i.t = d.chemin.t.that.i && d.batterie.t < distance[d.i.t, d.chemin.t.nextc.that.i]) => {
			// on est à un réceptacle et on doit charger
			d.batterie.t' = d.batterie.t.add[1]
			d.chemin.t' = d.chemin.t
		}
		else {
			d.i.t = d.chemin.t.that.i => d.chemin.t' = d.chemin.t.nextc
			else d.chemin.t' = d.chemin.t
			d.i.t != d.i.t' =>
				d.batterie.t' = d.batterie.t.sub[1]
			else
				d.batterie.t' = d.batterie.t
		}
		avancer[t, t', d]
		d.destination.t' = d.destination.t
		d.produits.t' = d.produits.t
	}
}

//avancer le drone d'un pas en x et si les x sont déjà alignés, avancer d'un pas en y
//TODO : si le drone ne peut pas avancer en x, tenter en y
pred avancer[t, t': Time, d: Drone] {
	d.i.t.x = d.chemin.t'.that.i.x => {
		d.i.t'.x = d.i.t.x
	} else {
		d.i.t.x < d.chemin.t'.that.i.x =>
			(intersectionDisponible[t,t',d,d.i.t.x.add[1],d.i.t.y] => d.i.t'.x = d.i.t.x.add[1] else d.i.t'.x = d.i.t.x)
		else
			(intersectionDisponible[t,t',d,d.i.t.x.sub[1],d.i.t.y] => d.i.t'.x = d.i.t.x.sub[1] else d.i.t'.x = d.i.t.x)	
	}
	d.i.t'.x != d.i.t.x =>
		d.i.t'.y = d.i.t.y
	else {
		d.i.t.y < d.chemin.t'.that.i.y => {
			intersectionDisponible[t,t',d,d.i.t.x,d.i.t.y.add[1]] => d.i.t'.y = d.i.t.y.add[1] else d.i.t'.y = d.i.t.y
		} else {
			d.i.t.y > d.chemin.t'.that.i.y =>
				(intersectionDisponible[t,t',d,d.i.t.x,d.i.t.y.sub[1]] => d.i.t'.y = d.i.t.y.sub[1] else d.i.t'.y = d.i.t.y)
			else
				d.i.t'.y = d.i.t.y
		}
	}
}

pred intersectionDisponible[t, t': Time, d: Drone, ix,iy: Int] {
	some e: Entrepot | {
		((e.i.x = ix && e.i.y = iy) || (all d': Drone | (d' != d && d'.i.t'.x = ix && d'.i.t'.y = iy) => (d'.batterie.t' = d'.batterie.t && d'.produits.t' = d'.produits.t)))
	}
}
/*
fact IlFautQueCaBouge {
	all t: Time - last | let t'=t.next |
		some d: Drone | d.i.t' = d.i.t => (d.produits.t' != d.produits.t || d.batterie.t' != d.batterie.t)
}
*/
/***** TESTS *****/

fact { Simulation }

assert PasDeDoublons {
	all p: Produit | all t: Time {
		all r: Receptacle | p in r.produits.t => {
			(no r': Receptacle | r != r' && p in r'.produits.t)
			(no d: Drone | p in d.produits.t)
			(one e: Entrepot | r = e => (lone c: Commande | p in c.produits.t) else (no c: Commande | p in c.produits.t))
		}
		all d: Drone | p in d.produits.t => {
			(no d': Drone | d != d' && p in d'.produits.t)
			(no r: Receptacle | p in r.produits.t)
			(no c: Commande | p in c.produits.t)
		}
	}
}
check PasDeDoublons for 2 Drone, 3 Receptacle, 8 Time, 4 Produit, 12 Intersection, exactly 2 Commande, 10 Chain, 4 Int

assert Pas2DronesMemeIntersection {
	one e: Entrepot | all t: Time | no disj d1,d2: Drone | d1.i.t = d2.i.t && d1.i.t != e.i
}
check Pas2DronesMemeIntersection for 2 Drone, 3 Receptacle, 8 Time, 4 Produit, 12 Intersection, exactly 2 Commande, 10 Chain, 4 Int

assert CapaciteBatterie {
	all d: Drone, t: Time | d.batterie.t >= 0 && d.batterie.t <= BCAP
}
check CapaciteBatterie for 1 Drone, 3 Receptacle, 8 Time, 4 Produit, 12 Intersection, exactly 2 Commande, 10 Chain, 4 Int

assert BatterieSeVide {
	all d: Drone, t: Time - last | let t' = t.next | d.i.t != d.i.t' => d.batterie.t' = d.batterie.t.sub[1]
}
check BatterieSeVide for 2 Drone, 3 Receptacle, 10 Time, 4 Produit, 12 Intersection, exactly 3 Commande, 10 Chain, 4 Int

/***** SIMULATION *****/

run Simulation for exactly 2 Drone, 2 Receptacle, 12 Time, 2 Produit, 10 Intersection, exactly 2 Commande, 10 Chain, 4 Int
// attention à ne pas contredire les faits NbDrones et NbReceptacles !
