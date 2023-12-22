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

one sig C2x2, C4, Q extends Group {}
one sig c2x21, c2x22, c2x23, c2x24, c41, c42, c43, c44, q0Hom1, q1Hom1, q1Hom2 extends Elements {}

	



	


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
// Claims that C2x2 is the direct product of C2 and C2 (i.e. non-cyclic abelian group of order 4)
fact {
	C2x2.element = (c2x21 + c2x22 + c2x23 + c2x24) and C2x2.id = c2x21 and C2x2.inv = ( c2x21 -> c2x21 + c2x22 -> c2x22 + c2x23 -> c2x23 + c2x24 -> c2x24) and C2x2.mult = ( c2x21 -> c2x21 -> c2x21 + c2x21 -> c2x22 -> c2x22 + c2x21 -> c2x23 -> c2x23 + c2x21 -> c2x24 -> c2x24 + c2x22 -> c2x21 -> c2x22 + c2x22 -> c2x22 -> c2x21 + c2x22 -> c2x23 -> c2x24 + c2x22 -> c2x24 -> c2x23 + c2x23 -> c2x21 -> c2x23 + c2x23 -> c2x22 -> c2x24 + c2x23 -> c2x23 -> c2x21 + c2x23 -> c2x24 -> c2x22 + c2x24 -> c2x21 -> c2x24 + c2x24 -> c2x22 -> c2x23 + c2x24 -> c2x23 -> c2x22 + c2x24 -> c2x24 -> c2x21) }
//Claims that C4 is the cyclic group of order 4
fact {
	C4.element = c41 + c42 + c43 + c44 and C4.id = c41 and C4.inv = ( c41 -> c41 + c42 -> c44 + c43 -> c43 + c44 -> c42) and C4.mult = (c41 -> c41 -> c41 + c41 -> c42 -> c42 + c41 -> c43 -> c43 + c41 -> c44 -> c44 + c42 -> c41 -> c42 + c42 -> c42 -> c43 + c42 -> c43 -> c44 + c42 -> c44 -> c41 + c43 -> c41 -> c43 + c43 -> c42 -> c44 + c43 -> c43 -> c41 + c43 -> c44 -> c42 + c44 -> c41 -> c44 + c44 -> c42 -> c41 + c44 -> c43 -> c42 + c44 -> c44 -> c43) }
//Claims that our quotient Q will have one of these sets of elements
fact {
	Q.element = q0Hom1 or Q.element = q1Hom1 + q1Hom2 }
//Produces all homomorphisms from C4 to C2x2 (note: fixing the elements of Q prevents redundant instances)
pred C4toC2x2 {
	all h : Hom | h.dom = C4 and h.ran = C2x2 and Q.element = q0Hom1 }

// The following 4 predicates produce each of the 4 homomorphisms from C4 to C2x2
pred C4toC2x20Hom[h : Hom] {
	h.dom = C4 and h.ran = C2x2 and h.map = ( c41 -> c2x21 + c42 -> c2x21 + c43 -> c2x21 + c44 -> c2x21 ) }
pred C4toC2x21Hom[h : Hom] {
	h.dom = C4 and h.ran = C2x2 and h.map = (c41 -> c2x21 + c42 -> c2x24 + c43 -> c2x21 + c44 -> c2x24) }
pred C4toC2x22Hom[h : Hom] {
	h.dom = C4 and h.ran = C2x2 and h.map = (c41 -> c2x21 + c42 -> c2x22 + c43 -> c2x21 + c44 -> c2x22) }
pred C4toC2x23Hom[h : Hom] {
	h.dom = C4 and h.ran = C2x2 and h.map = (c41 -> c2x21 + c42 -> c2x23 + c43 -> c2x21 + c44 -> c2x23) }
// The following 4 predicates produce the commutative diagram for each homomorphism from C4 to C2x2
pred C4toC2x20HomFIT[h : Hom] {
	some disj h1, h2 : Hom | C4toC2x20Hom[h] and Q.element = q0Hom1 and h1.dom = C4 and h1.ran = Q and h2.dom = Q and h2.ran = C2x2 and h.map = (h1.map).(h2.map) }
pred C4toC2x21HomFIT[h : Hom] {
	some disj h1, h2 : Hom | C4toC2x21Hom[h] and Q.element = q1Hom1 + q1Hom2 and Q.id = q1Hom1 and h1.dom = C4 and h1.ran = Q and h2.dom = Q and h2.ran = C2x2 and h.map = (h1.map).(h2.map) }
pred C4toC2x22HomFIT[h : Hom] {
	some disj h1, h2 : Hom | C4toC2x22Hom[h] and Q.element = q1Hom1 + q1Hom2 and Q.id = q1Hom1 and h1.dom = C4 and h1.ran = Q and h2.dom = Q and h2.ran = C2x2 and h.map = (h1.map).(h2.map) }
pred C4toC2x23HomFIT[h : Hom] {
	some disj h1, h2 : Hom | C4toC2x23Hom[h] and Q.element = q1Hom1 + q1Hom2 and Q.id = q1Hom1 and h1.dom = C4 and h1.ran = Q and h2.dom = Q and h2.ran = C2x2 and h.map = (h1.map).(h2.map) }

//Asserts that if we have a homomorphism from C4 to C2x2, then when we apply the First Isomorphism Theorem, then we will obtain one of 4 possible commutative diagrams
assert Main {
	all h : Hom | some disj h1, h2 : Hom | h.dom = C4 and h.ran = C2x2 and h1.dom = C4 and h1.ran = Q and h2.dom = Q and h2.ran = C2x2 implies (C4toC2x20HomFIT[h] or C4toC2x21HomFIT[h] or C4toC2x22HomFIT[h] or C4toC2x23HomFIT[h]) }
	


run C4toC2x2 for exactly 1 Hom, exactly 8 Elements, exactly 2 Group
run C4toC2x20Hom for exactly 1 Hom, exactly 8 Elements, exactly 2 Group
run C4toC2x21Hom for exactly 1 Hom, exactly 8 Elements, exactly 2 Group
run C4toC2x22Hom for exactly 1 Hom, exactly 8 Elements, exactly 2 Group
run C4toC2x23Hom for exactly 1 Hom, exactly 8 Elements, exactly 2 Group
run C4toC2x20HomFIT for exactly 3 Hom, exactly 9 Elements, exactly 3 Group
run C4toC2x21HomFIT for exactly 3 Hom, exactly 10 Elements, exactly 3 Group
run C4toC2x22HomFIT for exactly 3 Hom, exactly 10 Elements, exactly 3 Group
run C4toC2x23HomFIT for exactly 3 Hom, exactly 10 Elements, exactly 3 Group
check Main for exactly 3 Hom, exactly 10 Elements, exactly 3 Group





	 
	
