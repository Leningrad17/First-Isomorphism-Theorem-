open util/integer
//Signatures used to represent a Group
abstract sig Elements{}
abstract sig Group {
	element : set Elements,
	mult : element -> element -> one element,
	id : one element,
	inv : element -> one element
	}
sig Hom {
	dom : one Group,
	ran : one Group,
	map :set Elements -> set Elements }

one sig C6, C2, Q extends Group {}
one sig c61, c62, c63, c64, c65, c66, c27, c28, q0Hom9, q1Hom10, q1Hom11 extends Elements {}

	



	


//Eliminates unnecessary elements from the instance window
//pred CleanUp(e: Elements) {
	//some g: Group | e in g.element }

fact {
	all g1, g2 : Group | (g1.element = g2.element and g1.id =g2.id and g1.mult = g2.mult and g1.inv = g2.inv) iff g1 = g2 }

//Enforces the property that whenever you apply the binary operation to the identity element and any other element (which
//can include the identity as well), you return the other element (i.e., given a binary operation "x" and an arbitrary element e,
// e x id = e and id x e = e)
pred IdentityBinOpProperty(g : Group) {
	all g: Group | all e1 : g.element | (e1 in g.mult[g.id,e1]) and (e1 in g.mult[e1,g.id]) }


//Enforces the property that whenever you apply the binary operation to an element and its inverse (or vice versa), then you
//return the identity element of the group
pred InverseBinOpProperty(g : Group) {
	all g: Group | all e1 : g.element | g.mult[e1,g.inv[e1]] in g.id and g.mult[g.inv[e1],e1] in g.id}

//Enforces the property that whenever you apply the binary operation to three elements (not necessarily distinct), then 
//associativity holds (i.e. given a binary operation "x" and three arbitrary elements e1, e2, e3, then (e1 x e2) x e3 = e1 x (e2 x e3) )
pred AssociativityBinOpProperty(g: Group) {
	all g: Group | all e1, e2, e3: g.element | (g.mult[g.mult[e1,e2],e3] in g.mult[e1,g.mult[e2,e3]]) and (g.mult[e1,g.mult[e2,e3]] in g.mult[g.mult[e1,e2],e3]) }


	
	
//This predicate will create groups as defined in the axioms for groups (i.e. makes sure that in all instances, the Group atoms
// are indeed groups)
pred GroupDefinition(g: Group) {
	all g: Group | IdentityBinOpProperty[g]
	all g: Group | InverseBinOpProperty[g]
	all g: Group | AssociativityBinOpProperty[g]
	}

//Establishes the fact that all groups are groups
fact {
	all g: Group | GroupDefinition[g] }

//Will clean up the instance window for every instance
//fact {
//	all e : Elements | CleanUp[e] }


//Claims that for every group, the identity element of a group will be its own inverse
assert IdentityIsOwnInverse{
	all g: Group | g.inv[g.id] = g.id }

//Claims that every element of a group has a unique inverse
assert EachElementHasUniqueInverse{
	all g: Group | all disj e1, e2: g.element | (g.inv[e1] not in g.inv[e2]) and (g.inv[e2] not in g.inv[e1])}


//Claims that the map relation of every homomorphism will only consider mappings from the elements of the domain of the homomorphism to the elements of the range of the homomorphism
fact {
	all h: Hom | all g1, g2 : Elements |(g1 -> g2) in h.map implies (g2 in h.ran.element and g1 in h.dom.element) }

//Enforces that all homomorphisms must be functions
pred HomsAreFunctions(h : Hom) {
	all h: Hom | all g : h.dom.element | some h.map[g] and lone h.map[g] }

//Enforces the main property of a homomorphism, which is that for a homomorphism f: G -> H (where G and H are groups), for all g1, g2 in G, f(g1g2) = f(g1)f(g2)
pred HomsAreStructurePreserving (h:Hom) {
	all h: Hom | all g1, g2 : h.dom.element | (h.map[h.dom.mult[g1,g2]] in h.ran.mult[h.map[g1], h.map[g2]]) and (h.ran.mult[h.map[g1], h.map[g2]] in h.map[h.dom.mult[g1,g2]]) }

// Claims that all homomorphisms are functions and preserve structure
fact {
	all h: Hom | HomsAreFunctions[h] and HomsAreStructurePreserving[h] }

//Asserts that all homomorphisms will map the identity of the domain group to the identity of the range group
assert HomsMapIdentityToIdentity {
	all h: Hom | h.map[dom.id] = ran.id }

//Asserts that for all homomorphisms, the mapping of the inverse of an element of g is equal to the inverse of the mapping of the element g
assert HomMapofInverseEqualsInverseofHomMap {
	all h: Hom | all g: h.dom.element | h.map[h.dom.inv[g]] = h.ran.inv[h.map[g]] }


// Enforces the definition of C6 as the cyclic group of order 6
fact {
	C6.element = c61 + c62 + c63+ c64 + c65 + c66 and C6.id = c61 and C6.inv = (c61 -> c61 + c62 -> c66 + c63 -> c65 + c64 -> c64 + c65 -> c63 + c66 -> c62) and C6.mult = ( c61 -> c61 -> c61 + c61 -> c62 -> c62 + c62 -> c61 -> c62 + c61 -> c63 -> c63 + c63 -> c61 -> c63 + c61 -> c64 -> c64 + c64 -> c61 -> c64 +  c61 -> c65 -> c65 + c65 -> c61 -> c65 + c61 -> c66 -> c66 + c66 -> c61 -> c66 + c62 -> c62 -> c63 + c62 -> c63 -> c64 + c63 -> c62 -> c64 + c62 -> c64 -> c65 + c64 -> c62 -> c65 + c62 -> c65 -> c66 + c65 -> c62 -> c66 + c62 -> c66 -> c61 + c66 -> c62 -> c61 + c63 -> c63 -> c65 + c63 -> c64 -> c66 + c64 -> c63 -> c66 + c63 -> c65 -> c61 + c65 -> c63 -> c61 + c63 -> c66 -> c62 + c66 -> c63 -> c62 + c64 -> c64 -> c61 + c64 -> c65 -> c62 + c65 -> c64 -> c62 + c64 -> c66 -> c63 + c66 -> c64 -> c63 + c65 -> c65 -> c63 + c65 -> c66 -> c64 + c66 -> c65 -> c64 + c66 -> c66 -> c65)    }
//Enforces the definition of C2 as the cyclic group of order 2
fact {
	C2.element = c27 + c28 and C2.id = c27 }
// Enforces that our quotient group will be one of two groups
fact {
	(Q.element = q0Hom9) or (Q.element = q1Hom10 + q1Hom11 and Q.id = q1Hom10) }





//Produces the homomorphism which sends the generator of C6 to the identity of C2 (we'll call it the "0 Homomorphism")
pred C6toC20Hom[h : Hom] {
	h.dom = C6 and h.ran = C2 and h.map = (c61 -> c27 + c62 -> c27 + c63 -> c27 + c64 -> c27 + c65 -> c27 + c66 -> c27) and Q.element = q0Hom9 }
//Produces the homomorphism which sends the generator of C6 to the other element of C2 (we'll call it the "1 Homomorphism")
pred C6toC21Hom[h : Hom] {
	h.dom = C6 and h.ran = C2 and h.map = (c61 -> c27 + c62 -> c28 + c63 -> c27 + c64 -> c28 + c65 -> c27 + c66 -> c28) and Q.element = q1Hom10 + q1Hom11}

//Produces the unique commutative diagram for the 0 Homomorphism
pred C6toC20HomFIT[h : Hom] {
	some disj h1, h2 : Hom | C6toC20Hom[h] and Q.element = q0Hom9 and h1.dom = C6 and h1.ran = Q and h2.dom = Q and h2.ran = C2 and h.map = (h1.map).(h2.map) }


//Produces the unique commutative diagram for the 1 Homomorphism
pred C6toC21HomFIT[h : Hom]{
	some disj h1, h2 : Hom | C6toC21Hom[h] and Q.element = q1Hom10 + q1Hom11  and Q.id = q1Hom10 and h1.dom = C6 and h1.ran = Q and h2.dom = Q and h2.ran = C2 and h.map = (h1.map).(h2.map) }

// Asserts that if we have a homomorphism from C6 to C2, then when we apply the First Isomorphism Theorem, we will either get the 0 Hom diagram or the 1 Hom diagram
assert Main {
	all h : Hom |  some disj h1, h2 : Hom | h.dom = C6 and h.ran = C2 and h1.dom = C6 and h1.ran = Q and h2.dom = Q and h2.ran = C2 implies (C6toC20HomFIT[h] or C6toC21HomFIT[h]) }

run C6toC20Hom for  11 Elements, exactly 1 Hom, exactly 2 Group
run C6toC21Hom for exactly 8 Elements, exactly 1 Hom, exactly 3 Group
run C6toC20HomFIT for exactly 9 Elements, exactly 3 Hom, exactly 3 Group
run C6toC21HomFIT for exactly 11 Elements, exactly 3 Hom, exactly 3 Group
check Main for exactly 11 Elements, exactly 3 Hom, exactly 3 Group
