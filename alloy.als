//permet de faire des sommes, des produits...
open util/integer
//permet d'utiliser time.next pour se déplacer dans le temps
open util/ordering[Time]

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
	batterie: Int one->Time,
	bloquePar: Drone->Time
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

//on a au moins 1 drone
fact NbDrones { #Drone > 0 }

//on a au moins 2 réceptacles (dont l'entrepôt)
fact NbReceptacles { #Receptacle > 1 }

//deux intersections ne partagent pas la même position
fact IntersectionsSeparees { all disj i1, i2: Intersection | i1.x != i2.x || i1.y != i2.y }

//deux réceptacles ne sont pas à la même position
fact ReceptaclesSepares { all disj r1, r2: Receptacle | r1.i != r2.i }

//les drones ne peuvent porter plus de DCAP produits
fact CapaciteDrone { all d: Drone, t: Time | #d.produits.t <= DCAP }

//les réceptacles ne peuvent contenir plus de RCAP produits
//TODO et si plus de RCAP produits doivent être livrés à ce réceptacle ? On le vide pas de temps à autre ?
fact CapaciteReceptacle { all r: Receptacle, t: Time | #r.produits.t <= RCAP }

/***** CHEMIN ****/

//"liste chaînée" de réceptacles permettant de relier 2 réceptacles
sig Chain {
	that : one Receptacle,
	nextc : lone Chain
}

//deux Chain différents ont au moins 1 champ différent (intersection ou Chain suivant)
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

//la liste chaînée ne comporte pas de boucle
fact PasDeBoucle {
	all c: Chain | c.that not in c.^nextc.that
}

//donne la première étape du chemin partant de depr et allant à arrr
pred Chemin[depr, arrr: Receptacle, chemin: Chain] {
	one arr: Chain | {
		chemin.that = depr
		arr.that = arrr
		no arr.nextc //fin de la chaîne : pointe sur rien
		arr in chemin.*nextc //on atteint l'arrivée en partant du départ
	}
}

/***** Simulation *****/

//initialisation de la simulation
pred init[t: Time] {
	//pas de produits dans les drones
	no Drone.produits.t
	//aucune commande vide
	all c: Commande | #c.produits.t > 0
	one e: Entrepot | {
		//soit r est l'entrepôt, soit c'est un réceptacle et donc pas de produit.
		all r: Receptacle | r = e || no r.produits.t
		//tous les drones chargés à bloc, à l'entrepôt
		all d: Drone | {
			d.i.t = e.i
			d.destination.t = e
			d.chemin.t.that = e
			d.batterie.t = BCAP
		}
		//tous les produits à l'entrepôt, et dans une seule commande
		all p: Produit | p in e.produits.t && one c: Commande | p in c.produits.t
	}
}

//exécute toute la simulation
pred Simulation {
	init[first]
	all t: Time - last | let t' = t.next | -- between each timestep
	{
		// déplacement du drone
		all d: Drone | majDrone[t,t',d]
		// màj produits entrepot : on enlève de l'entrepôt les produits étant dans des drones
		all p: Produit | one e: Entrepot | 
			(p in e.produits.t && (no d: Drone | p in d.produits.t')) => 
			p in e.produits.t' 
			else p not in e.produits.t'
		// màj produits des commandes : les produits qui sont dans des drones ne sont plus dans les commandes
		all c: Commande, p: Produit | 
			(p in c.produits.t && (no d: Drone | p in d.produits.t')) => 
			p in c.produits.t' 
			else p not in c.produits.t'
		// màj produits des réceptacles : si aucun drone n'est arrivé au réceptacle, les produits ne changent pas
		all r: Receptacle | (no d: Drone | d.destination.t = r && d.i.t = r.i) => r.produits.t' = r.produits.t
	}
}

pred majDrone[t, t': Time, d: Drone] {
	one e: Entrepot | 
	d.i.t = d.destination.t.i => { // drone à destination
		d.i.t = e.i => { // drone à l'entrepôt

			//on cherche une commande non vide, qui n'a pas été prise par un drone
			(no c: Commande | #c.produits.t > 0 && no d': Drone | d != d' && c.produits.t in d'.produits.t') => {
				//il n'y a plus de commande : le drone reste à l'entrepôt
				d.produits.t' = d.produits.t
				d.destination.t' = d.destination.t
				d.chemin.t' = d.chemin.t
				d.batterie.t' = d.batterie.t
				d.i.t' = d.i.t
			}
			else one c: {c: Commande | #c.produits.t > 0 && no d': Drone | d != d' && c.produits.t in d'.produits.t'} | {
				//on charge la commande
				#d.produits.t' = DCAP || #c.produits.t' = 0 //on charge au maximum de la capacité du drone
				d.produits.t' in c.produits.t
				d.produits.t' not in c.produits.t'
				no d': Drone | d' != d && some d.produits.t' & d'.produits.t' //le produit est dans 1 seul drone
				d.destination.t' = c.adresse
				Chemin[e, c.adresse, d.chemin.t']
			}
		} else { //on livre une commande à un réceptacle : décharger les produits
			no d.produits.t'
			d.destination.t.produits.t' = (d.destination.t.produits.t + d.produits.t)
			d.destination.t' = e
			Chemin[d.destination.t, e, d.chemin.t']
		}
		//le drone est immobile : la position et la batterie sont intactes
		d.i.t' = d.i.t
		d.batterie.t' = d.batterie.t
		no d.bloquePar.t
	} else { // drone en chemin
		//si nous sommes à un réceptacle et que nous n'avons pas assez de batterie pour atteindre le prochain
		(d.i.t = d.chemin.t.that.i && d.batterie.t < distance[d.i.t, d.chemin.t.nextc.that.i]) => {
			//on doit charger la batterie
			d.batterie.t' = d.batterie.t.add[1]
			d.chemin.t' = d.chemin.t
			no d.bloquePar.t
			d.i.t' = d.i.t
		}
		else {
			//passer à l'étape suivante de l'itinéraire si besoin
			d.i.t = d.chemin.t.that.i => d.chemin.t' = d.chemin.t.nextc
			else d.chemin.t' = d.chemin.t
			//décharger la batterie si le drone s'est déplacé
			d.i.t != d.i.t' =>
				d.batterie.t' = d.batterie.t.sub[1]
			else
				d.batterie.t' = d.batterie.t

			//calculer la position suivante
			avancer[t, t', d]
		}
		//ne pas changer la destination et les produits
		d.destination.t' = d.destination.t
		d.produits.t' = d.produits.t
	}
}

//avancer le drone d'un pas en x et si le x est déjà aligné avec la destination, avancer d'un pas en y
pred avancer[t, t': Time, d: Drone] {
	d.chemin.t'.that.i.x != d.i.t.x => {
		//on essaie d'avancer en x
		d.i.t.x < d.chemin.t'.that.i.x => {
			intersectionDisponible[t,t',d,d.i.t.x.add[1],d.i.t.y]
			(no d.bloquePar.t) => d.i.t'.x = d.i.t.x.add[1] else d.i.t'.x = d.i.t.x
		} else {
			intersectionDisponible[t,t',d,d.i.t.x.sub[1],d.i.t.y] 
			(no d.bloquePar.t) => d.i.t'.x = d.i.t.x.sub[1] else d.i.t'.x = d.i.t.x
		}	
		d.i.t'.y = d.i.t.y
	} else {
		d.i.t'.x = d.i.t.x
		//on essaie d'avancer en y
		d.i.t.y < d.chemin.t'.that.i.y => {
			intersectionDisponible[t,t',d,d.i.t.x,d.i.t.y.add[1]]
			(no d.bloquePar.t) => d.i.t'.y = d.i.t.y.add[1] else d.i.t'.y = d.i.t.y
		} else {
			d.i.t.y > d.chemin.t'.that.i.y => {
				intersectionDisponible[t,t',d,d.i.t.x,d.i.t.y.sub[1]]
				(no d.bloquePar.t) => d.i.t'.y = d.i.t.y.sub[1] else d.i.t'.y = d.i.t.y
			} else {
				//on est déjà arrivé
				d.i.t'.y = d.i.t.y
				no d.bloquePar.t
			}
		}
	}
}

//vérifie si l'intersection aux coordonnées ix et iy est disponible, et met à jour le champ bloquePar
//du drone en fonction du résultat.
pred intersectionDisponible[t, t': Time, d: Drone, ix,iy: Int] {
	some e: Entrepot | e.i.x = ix && e.i.y = iy => no d.bloquePar.t
	else {
		(all d': Drone | estNonBloqueur[t, t', d, d', ix, iy] => d' not in d.bloquePar.t else d' in d.bloquePar.t)
	}
}

//vérifie si le drone d' bloque le drone d qui tente d'aller en ix, iy entre l'instant t et t'
pred estNonBloqueur[t, t': Time, d, d': Drone, ix,iy: Int] {
	//si le drone peut être problématique (même intersection)...
	(d' != d && d'.i.t'.x = ix && d'.i.t'.y = iy) =>
		//le drone d' doit bloquer la progression s'il fait quelque chose (avancer, se recharger, livrer)
		(d'.batterie.t' = d'.batterie.t && d'.produits.t' = d'.produits.t &&
		//... ou s'il ne fait pas partie d'une file de drones bloqués (c'est alors une boucle, ou deux drones qui se font
		//face à face ; on souhaiterait qu'ils se déplacent) 
		!(some dNB: d'.*(bloquePar.t) | no dNB.bloquePar.t))
}

/***** CONSTANTES *****/
// taille de la carte (0..MAPSIZE-1)^2
let MAPSIZE = 2
// capacité des réceptacles
let RCAP = 7
// capacité des drones
let DCAP = 2
// capacité de la batterie
let BCAP = 3

/***** TESTS *****/
//MAPSIZE=3 conseillé

fact { Simulation }

//aucune duplication de produits : ils sont dans UN SEUL réceptacle OU dans UN drone
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

//deux drones ne partagent jamais la même intersection (sauf à l'entrepôt)
//long (dizaines de minutes) mais il est nécessaire d'avoir 3 drones/commandes/produits car des problèmes de collision
//sont apparus lors du passage de 2 à 3 drones.
assert Pas2DronesMemeIntersection {
	one e: Entrepot | all t: Time | no disj d1,d2: Drone | d1.i.t = d2.i.t && d1.i.t != e.i
}
check Pas2DronesMemeIntersection for exactly 3 Drone, 2 Receptacle, 8 Time, 3 Produit, 10 Intersection, exactly 3 Commande, 10 Chain, 4 Int

//la capacité de la batterie est toujours entre 0 et DCAP
//~15 min sur mon PC (TODO trop long !)
assert CapaciteBatterie {
	all d: Drone, t: Time | d.batterie.t >= 0 && d.batterie.t <= BCAP
}
check CapaciteBatterie for 2 Drone, 2 Receptacle, 10 Time, 2 Produit, 10 Intersection, exactly 2 Commande, 10 Chain, 4 Int

//la batterie se vide de 1 unité lorsque le drone se déplace
assert BatterieSeVide {
	all d: Drone, t: Time - last | let t' = t.next | d.i.t != d.i.t' => d.batterie.t' = d.batterie.t.sub[1]
}
check BatterieSeVide for 1 Drone, 3 Receptacle, 10 Time, 4 Produit, 12 Intersection, exactly 3 Commande, 10 Chain, 4 Int

//la simulation se termine (tous les drones sont à l'entrepôt, tous les produits sont à leur destination)
//Il faut que MAPSIZE=2 (?)
assert FinSimulation {
	one e: Entrepot | some t: Time {
		all c: Commande | {
			#c.produits.t = 0
			all p: c.produits.first | p in c.adresse.produits.t
		}
		all d: Drone {
			#d.produits.t = 0
			d.i.t = e.i
		}
	}
}
check FinSimulation for exactly 2 Drone, 2 Receptacle, 23 Time, exactly 6 Produit, 10 Intersection, exactly 2 Commande, 10 Chain, 4 Int

//les drones ne se déplacent jamais d'une distance de plus de 1
assert AucuneTeleportation {
	all d: Drone, t: Time - last | let t' = t.next | distance[d.i.t, d.i.t'] <= 1
}
check AucuneTeleportation for exactly 4 Drone, 2 Receptacle, 10 Time, 2 Produit, 10 Intersection, exactly 2 Commande, 10 Chain, 4 Int

/***** Exécution de la simulation *****/

//simule avec un réceptacle en (0, 3) et un entrepôt en (0, 0).
//les drones doivent alors suivre une ligne, ce qui teste bien leur capacité à se croiser sans bloquer.
//il faut que MAPSIZE >= 4 (prend quelques minutes)
pred SimulationLigne {
	Simulation && all e: Entrepot | all r: Receptacle | r.i.x = 0 && (r = e => r.i.y = 0 else r.i.y = 3)
}
run SimulationLigne for exactly 3 Drone, 2 Receptacle, 25 Time, exactly 3 Produit, 10 Intersection, exactly 3 Commande, 10 Chain, 4 Int

//générer une simulation avec 3 drones, 1 réceptacle + entrepôt, et 3 commandes.
//MAPSIZE=3 conseillé
run Simulation for exactly 3 Drone, 2 Receptacle, 15 Time, exactly 3 Produit, 10 Intersection, exactly 3 Commande, 10 Chain, 4 Int

//générer une simulation avec 3 drones, 2 réceptacles + entrepôt, et 3 commandes.
//MAPSIZE=3 conseillé
run Simulation for exactly 3 Drone, 3 Receptacle, 15 Time, exactly 3 Produit, 10 Intersection, exactly 3 Commande, 10 Chain, 4 Int

//générer une simulation qui démontre la gestion de la capacité des drones
//MAPSIZE=2 conseillé
run Simulation for exactly 4 Drone, exactly 3 Receptacle, 15 Time, exactly 8 Produit, 10 Intersection, exactly 2 Commande, 10 Chain, 4 Int
