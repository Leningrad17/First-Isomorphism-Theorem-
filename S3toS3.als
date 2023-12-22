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

one sig S3, Q extends Group {}
one sig S31, S32, S33, S34, S35, S36, qAuto1, qAuto2, qAuto3, qAuto4, qAuto5, qAuto6, q0Hom1, q1Hom1, q1Hom2  extends Elements {}

	



	


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

//Note : Useful for generating homomorphisms but once we add in the quotient group, this predicate becomes unreliable
//pred S3toS3Homs {
	//all h: Hom | h.dom = S3 and h.ran = S3 }

// Asserts that S3 is the symmetric group of order 6
fact {
	S3.element = (S31 + S32 + S33 + S34 + S35 + S36) and S3.id = S31 and S3.inv = (S31 -> S31 + S32 -> S32 + S33 -> S33 + S34 -> S34 + S35 -> S36 + S36 -> S35) and S3.mult = (S31 -> S31 -> S31) + (S31 -> S32 -> S32) + (S31 -> S33 -> S33) + (S31 -> S34 -> S34) + (S31 -> S35 -> S35) + (S31 -> S36 -> S36) + (S32 -> S31 -> S32) + (S32 -> S32 -> S31) + (S32 -> S33 -> S35) + (S32 -> S34 -> S36) + (S32 -> S35 -> S33) + (S32 -> S36 -> S34)+ (S33 -> S31 -> S33) + (S33 -> S32 -> S36) + (S33 -> S33 -> S31) + (S33 -> S34 -> S35) + (S33 -> S35 -> S34) + (S33 -> S36 -> S32)+ (S34 -> S31 -> S34) + (S34 -> S32 -> S35) + (S34 -> S33 -> S36) + (S34 -> S34 -> S31) + (S34 -> S35 -> S32) + (S34 -> S36 -> S33)+ (S35 -> S31 -> S35) + (S35 -> S32 -> S34) + (S35 -> S33 -> S32) + (S35 -> S34 -> S33) + (S35 -> S35 -> S36) + (S35 -> S36 -> S31)+ (S36 -> S31 -> S36) + (S36 -> S32 -> S33) + (S36 -> S33 -> S34) + (S36 -> S34 -> S32) + (S36 -> S35 -> S31) + (S36 -> S36 -> S35) }
// Asserts that our quotient group Q will have one of these sets of elements
fact {
	Q.element = qAuto1 + qAuto2 + qAuto3 + qAuto4 + qAuto5 + qAuto6 or Q.element = q0Hom1 or Q.element = q1Hom1 + q1Hom2 }

// These predicates produce all of the possible homomorphisms between S3 and S3, with 6 of them being automorphisms and 4 of them being strictly homomorphisms
pred S3toS3Auto1[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S34 + S33 -> S32 + S34 -> S33 + S35 -> S35 + S36 -> S36) and Q.element =  qAuto1 + qAuto2 + qAuto3 + qAuto4 + qAuto5 + qAuto6 and Q.id = qAuto1 and Q.inv = (qAuto1 -> qAuto1 + qAuto2 -> qAuto2 + qAuto3 -> qAuto3 + qAuto4 -> qAuto4 + qAuto5 -> qAuto6 + qAuto6 -> qAuto5) and Q.mult = (qAuto1 -> qAuto1 -> qAuto1) + (qAuto1 -> qAuto2 -> qAuto2) + (qAuto1 -> qAuto3 -> qAuto3) + (qAuto1 -> qAuto4 -> qAuto4) + (qAuto1 -> qAuto5 -> qAuto5) + (qAuto1 -> qAuto6 -> qAuto6) + (qAuto2 -> qAuto1 -> qAuto2) + (qAuto2 -> qAuto2 -> qAuto1) + (qAuto2 -> qAuto3 -> qAuto5) + (qAuto2 -> qAuto4 -> qAuto6) + (qAuto2 -> qAuto5 -> qAuto3) + (qAuto2 -> qAuto6 -> qAuto4)+ (qAuto3 -> qAuto1 -> qAuto3) + (qAuto3 -> qAuto2 -> qAuto6) + (qAuto3 -> qAuto3 -> qAuto1) + (qAuto3 -> qAuto4 -> qAuto5) + (qAuto3 -> qAuto5 -> qAuto4) + (qAuto3 -> qAuto6 -> qAuto2)+ (qAuto4 -> qAuto1 -> qAuto4) + (qAuto4 -> qAuto2 -> qAuto5) + (qAuto4 -> qAuto3 -> qAuto6) + (qAuto4 -> qAuto4 -> qAuto1) + (qAuto4 -> qAuto5 -> qAuto2) + (qAuto4 -> qAuto6 -> qAuto3)+ (qAuto5 -> qAuto1 -> qAuto5) + (qAuto5 -> qAuto2 -> qAuto4) + (qAuto5 -> qAuto3 -> qAuto2) + (qAuto5 -> qAuto4 -> qAuto3) + (qAuto5 -> qAuto5 -> qAuto6) + (qAuto5 -> qAuto6 -> qAuto1)+ (qAuto6 -> qAuto1 -> qAuto6) + (qAuto6 -> qAuto2 -> qAuto3) + (qAuto6 -> qAuto3 -> qAuto4) + (qAuto6 -> qAuto4 -> qAuto2) + (qAuto6 -> qAuto5 -> qAuto1) + (qAuto6 -> qAuto6 -> qAuto5) }
pred S3toS3Auto2[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S32 + S33 -> S34 + S34 -> S33 + S35 -> S36 + S36 -> S35) }
pred S3toS3Auto3[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S32 + S33 -> S33 + S34 -> S34 + S35 -> S35 + S36 -> S36) }
pred S3toS3Auto4[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S33 + S33 -> S34 + S34 -> S32 + S35 -> S35 + S36 -> S36) }
pred S3toS3Auto5[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S33 + S33 -> S32 + S34 -> S34 + S35 -> S36 + S36 -> S35) }
pred S3toS3Auto6[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S34 + S33 -> S33 + S34 -> S32 + S35 -> S36 + S36 -> S35) }
pred S3toS3Hom0[h: Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S31 + S33 -> S31 + S34 -> S31 + S35 -> S31 + S36 -> S31) }
pred S3toS3Hom1[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S32 + S33 -> S32 + S34 -> S32 + S35 -> S31 + S36 -> S31) }
pred S3toS3Hom2[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S33 + S33 -> S33 + S34 -> S33 + S35 -> S31 + S36 -> S31) }
pred S3toS3Hom3[h : Hom] {
	h.dom = S3 and h.ran = S3 and h.map = ( S31 -> S31 + S32 -> S34 + S33 -> S34 + S34 -> S34 + S35 -> S31 + S36 -> S31) }

//The following six predicates produce the unique commutative diagram for each automorphism of S3 (note that we have to explicitly define the mapping for h1)
pred S3toS3Auto1FIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Auto1[h] and Q.element =  qAuto1 + qAuto2 + qAuto3 + qAuto4 + qAuto5 + qAuto6 and Q.id = qAuto1 and Q.inv = (qAuto1 -> qAuto1 + qAuto2 -> qAuto2 + qAuto3 -> qAuto3 + qAuto4 -> qAuto4 + qAuto5 -> qAuto6 + qAuto6 -> qAuto5) and Q.mult = (qAuto1 -> qAuto1 -> qAuto1) + (qAuto1 -> qAuto2 -> qAuto2) + (qAuto1 -> qAuto3 -> qAuto3) + (qAuto1 -> qAuto4 -> qAuto4) + (qAuto1 -> qAuto5 -> qAuto5) + (qAuto1 -> qAuto6 -> qAuto6) + (qAuto2 -> qAuto1 -> qAuto2) + (qAuto2 -> qAuto2 -> qAuto1) + (qAuto2 -> qAuto3 -> qAuto5) + (qAuto2 -> qAuto4 -> qAuto6) + (qAuto2 -> qAuto5 -> qAuto3) + (qAuto2 -> qAuto6 -> qAuto4)+ (qAuto3 -> qAuto1 -> qAuto3) + (qAuto3 -> qAuto2 -> qAuto6) + (qAuto3 -> qAuto3 -> qAuto1) + (qAuto3 -> qAuto4 -> qAuto5) + (qAuto3 -> qAuto5 -> qAuto4) + (qAuto3 -> qAuto6 -> qAuto2)+ (qAuto4 -> qAuto1 -> qAuto4) + (qAuto4 -> qAuto2 -> qAuto5) + (qAuto4 -> qAuto3 -> qAuto6) + (qAuto4 -> qAuto4 -> qAuto1) + (qAuto4 -> qAuto5 -> qAuto2) + (qAuto4 -> qAuto6 -> qAuto3)+ (qAuto5 -> qAuto1 -> qAuto5) + (qAuto5 -> qAuto2 -> qAuto4) + (qAuto5 -> qAuto3 -> qAuto2) + (qAuto5 -> qAuto4 -> qAuto3) + (qAuto5 -> qAuto5 -> qAuto6) + (qAuto5 -> qAuto6 -> qAuto1)+ (qAuto6 -> qAuto1 -> qAuto6) + (qAuto6 -> qAuto2 -> qAuto3) + (qAuto6 -> qAuto3 -> qAuto4) + (qAuto6 -> qAuto4 -> qAuto2) + (qAuto6 -> qAuto5 -> qAuto1) + (qAuto6 -> qAuto6 -> qAuto5) and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h1.map = (S31 -> qAuto1 + S32 -> qAuto2 + S33 -> qAuto3 + S34 -> qAuto4 + S35 -> qAuto5 + S36 -> qAuto6) and h.map = (h1.map).(h2.map) }   
pred S3toS3Auto2FIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Auto2[h] and Q.element =  qAuto1 + qAuto2 + qAuto3 + qAuto4 + qAuto5 + qAuto6 and Q.id = qAuto1 and Q.inv = (qAuto1 -> qAuto1 + qAuto2 -> qAuto2 + qAuto3 -> qAuto3 + qAuto4 -> qAuto4 + qAuto5 -> qAuto6 + qAuto6 -> qAuto5) and Q.mult = (qAuto1 -> qAuto1 -> qAuto1) + (qAuto1 -> qAuto2 -> qAuto2) + (qAuto1 -> qAuto3 -> qAuto3) + (qAuto1 -> qAuto4 -> qAuto4) + (qAuto1 -> qAuto5 -> qAuto5) + (qAuto1 -> qAuto6 -> qAuto6) + (qAuto2 -> qAuto1 -> qAuto2) + (qAuto2 -> qAuto2 -> qAuto1) + (qAuto2 -> qAuto3 -> qAuto5) + (qAuto2 -> qAuto4 -> qAuto6) + (qAuto2 -> qAuto5 -> qAuto3) + (qAuto2 -> qAuto6 -> qAuto4)+ (qAuto3 -> qAuto1 -> qAuto3) + (qAuto3 -> qAuto2 -> qAuto6) + (qAuto3 -> qAuto3 -> qAuto1) + (qAuto3 -> qAuto4 -> qAuto5) + (qAuto3 -> qAuto5 -> qAuto4) + (qAuto3 -> qAuto6 -> qAuto2)+ (qAuto4 -> qAuto1 -> qAuto4) + (qAuto4 -> qAuto2 -> qAuto5) + (qAuto4 -> qAuto3 -> qAuto6) + (qAuto4 -> qAuto4 -> qAuto1) + (qAuto4 -> qAuto5 -> qAuto2) + (qAuto4 -> qAuto6 -> qAuto3)+ (qAuto5 -> qAuto1 -> qAuto5) + (qAuto5 -> qAuto2 -> qAuto4) + (qAuto5 -> qAuto3 -> qAuto2) + (qAuto5 -> qAuto4 -> qAuto3) + (qAuto5 -> qAuto5 -> qAuto6) + (qAuto5 -> qAuto6 -> qAuto1)+ (qAuto6 -> qAuto1 -> qAuto6) + (qAuto6 -> qAuto2 -> qAuto3) + (qAuto6 -> qAuto3 -> qAuto4) + (qAuto6 -> qAuto4 -> qAuto2) + (qAuto6 -> qAuto5 -> qAuto1) + (qAuto6 -> qAuto6 -> qAuto5) and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h1.map = (S31 -> qAuto1 + S32 -> qAuto2 + S33 -> qAuto3 + S34 -> qAuto4 + S35 -> qAuto5 + S36 -> qAuto6) and h.map = (h1.map).(h2.map) }
pred S3toS3Auto3FIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Auto3[h] and Q.element =  qAuto1 + qAuto2 + qAuto3 + qAuto4 + qAuto5 + qAuto6 and Q.id = qAuto1 and Q.inv = (qAuto1 -> qAuto1 + qAuto2 -> qAuto2 + qAuto3 -> qAuto3 + qAuto4 -> qAuto4 + qAuto5 -> qAuto6 + qAuto6 -> qAuto5) and Q.mult = (qAuto1 -> qAuto1 -> qAuto1) + (qAuto1 -> qAuto2 -> qAuto2) + (qAuto1 -> qAuto3 -> qAuto3) + (qAuto1 -> qAuto4 -> qAuto4) + (qAuto1 -> qAuto5 -> qAuto5) + (qAuto1 -> qAuto6 -> qAuto6) + (qAuto2 -> qAuto1 -> qAuto2) + (qAuto2 -> qAuto2 -> qAuto1) + (qAuto2 -> qAuto3 -> qAuto5) + (qAuto2 -> qAuto4 -> qAuto6) + (qAuto2 -> qAuto5 -> qAuto3) + (qAuto2 -> qAuto6 -> qAuto4)+ (qAuto3 -> qAuto1 -> qAuto3) + (qAuto3 -> qAuto2 -> qAuto6) + (qAuto3 -> qAuto3 -> qAuto1) + (qAuto3 -> qAuto4 -> qAuto5) + (qAuto3 -> qAuto5 -> qAuto4) + (qAuto3 -> qAuto6 -> qAuto2)+ (qAuto4 -> qAuto1 -> qAuto4) + (qAuto4 -> qAuto2 -> qAuto5) + (qAuto4 -> qAuto3 -> qAuto6) + (qAuto4 -> qAuto4 -> qAuto1) + (qAuto4 -> qAuto5 -> qAuto2) + (qAuto4 -> qAuto6 -> qAuto3)+ (qAuto5 -> qAuto1 -> qAuto5) + (qAuto5 -> qAuto2 -> qAuto4) + (qAuto5 -> qAuto3 -> qAuto2) + (qAuto5 -> qAuto4 -> qAuto3) + (qAuto5 -> qAuto5 -> qAuto6) + (qAuto5 -> qAuto6 -> qAuto1)+ (qAuto6 -> qAuto1 -> qAuto6) + (qAuto6 -> qAuto2 -> qAuto3) + (qAuto6 -> qAuto3 -> qAuto4) + (qAuto6 -> qAuto4 -> qAuto2) + (qAuto6 -> qAuto5 -> qAuto1) + (qAuto6 -> qAuto6 -> qAuto5) and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h1.map = (S31 -> qAuto1 + S32 -> qAuto2 + S33 -> qAuto3 + S34 -> qAuto4 + S35 -> qAuto5 + S36 -> qAuto6) and h.map = (h1.map).(h2.map) }
pred S3toS3Auto4FIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Auto4[h] and Q.element =  qAuto1 + qAuto2 + qAuto3 + qAuto4 + qAuto5 + qAuto6 and Q.id = qAuto1 and Q.inv = (qAuto1 -> qAuto1 + qAuto2 -> qAuto2 + qAuto3 -> qAuto3 + qAuto4 -> qAuto4 + qAuto5 -> qAuto6 + qAuto6 -> qAuto5) and Q.mult = (qAuto1 -> qAuto1 -> qAuto1) + (qAuto1 -> qAuto2 -> qAuto2) + (qAuto1 -> qAuto3 -> qAuto3) + (qAuto1 -> qAuto4 -> qAuto4) + (qAuto1 -> qAuto5 -> qAuto5) + (qAuto1 -> qAuto6 -> qAuto6) + (qAuto2 -> qAuto1 -> qAuto2) + (qAuto2 -> qAuto2 -> qAuto1) + (qAuto2 -> qAuto3 -> qAuto5) + (qAuto2 -> qAuto4 -> qAuto6) + (qAuto2 -> qAuto5 -> qAuto3) + (qAuto2 -> qAuto6 -> qAuto4)+ (qAuto3 -> qAuto1 -> qAuto3) + (qAuto3 -> qAuto2 -> qAuto6) + (qAuto3 -> qAuto3 -> qAuto1) + (qAuto3 -> qAuto4 -> qAuto5) + (qAuto3 -> qAuto5 -> qAuto4) + (qAuto3 -> qAuto6 -> qAuto2)+ (qAuto4 -> qAuto1 -> qAuto4) + (qAuto4 -> qAuto2 -> qAuto5) + (qAuto4 -> qAuto3 -> qAuto6) + (qAuto4 -> qAuto4 -> qAuto1) + (qAuto4 -> qAuto5 -> qAuto2) + (qAuto4 -> qAuto6 -> qAuto3)+ (qAuto5 -> qAuto1 -> qAuto5) + (qAuto5 -> qAuto2 -> qAuto4) + (qAuto5 -> qAuto3 -> qAuto2) + (qAuto5 -> qAuto4 -> qAuto3) + (qAuto5 -> qAuto5 -> qAuto6) + (qAuto5 -> qAuto6 -> qAuto1)+ (qAuto6 -> qAuto1 -> qAuto6) + (qAuto6 -> qAuto2 -> qAuto3) + (qAuto6 -> qAuto3 -> qAuto4) + (qAuto6 -> qAuto4 -> qAuto2) + (qAuto6 -> qAuto5 -> qAuto1) + (qAuto6 -> qAuto6 -> qAuto5) and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h1.map = (S31 -> qAuto1 + S32 -> qAuto2 + S33 -> qAuto3 + S34 -> qAuto4 + S35 -> qAuto5 + S36 -> qAuto6) and h.map = (h1.map).(h2.map) }
pred S3toS3Auto5FIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Auto5[h] and Q.element =  qAuto1 + qAuto2 + qAuto3 + qAuto4 + qAuto5 + qAuto6 and Q.id = qAuto1 and Q.inv = (qAuto1 -> qAuto1 + qAuto2 -> qAuto2 + qAuto3 -> qAuto3 + qAuto4 -> qAuto4 + qAuto5 -> qAuto6 + qAuto6 -> qAuto5) and Q.mult = (qAuto1 -> qAuto1 -> qAuto1) + (qAuto1 -> qAuto2 -> qAuto2) + (qAuto1 -> qAuto3 -> qAuto3) + (qAuto1 -> qAuto4 -> qAuto4) + (qAuto1 -> qAuto5 -> qAuto5) + (qAuto1 -> qAuto6 -> qAuto6) + (qAuto2 -> qAuto1 -> qAuto2) + (qAuto2 -> qAuto2 -> qAuto1) + (qAuto2 -> qAuto3 -> qAuto5) + (qAuto2 -> qAuto4 -> qAuto6) + (qAuto2 -> qAuto5 -> qAuto3) + (qAuto2 -> qAuto6 -> qAuto4)+ (qAuto3 -> qAuto1 -> qAuto3) + (qAuto3 -> qAuto2 -> qAuto6) + (qAuto3 -> qAuto3 -> qAuto1) + (qAuto3 -> qAuto4 -> qAuto5) + (qAuto3 -> qAuto5 -> qAuto4) + (qAuto3 -> qAuto6 -> qAuto2)+ (qAuto4 -> qAuto1 -> qAuto4) + (qAuto4 -> qAuto2 -> qAuto5) + (qAuto4 -> qAuto3 -> qAuto6) + (qAuto4 -> qAuto4 -> qAuto1) + (qAuto4 -> qAuto5 -> qAuto2) + (qAuto4 -> qAuto6 -> qAuto3)+ (qAuto5 -> qAuto1 -> qAuto5) + (qAuto5 -> qAuto2 -> qAuto4) + (qAuto5 -> qAuto3 -> qAuto2) + (qAuto5 -> qAuto4 -> qAuto3) + (qAuto5 -> qAuto5 -> qAuto6) + (qAuto5 -> qAuto6 -> qAuto1)+ (qAuto6 -> qAuto1 -> qAuto6) + (qAuto6 -> qAuto2 -> qAuto3) + (qAuto6 -> qAuto3 -> qAuto4) + (qAuto6 -> qAuto4 -> qAuto2) + (qAuto6 -> qAuto5 -> qAuto1) + (qAuto6 -> qAuto6 -> qAuto5) and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h1.map = (S31 -> qAuto1 + S32 -> qAuto2 + S33 -> qAuto3 + S34 -> qAuto4 + S35 -> qAuto5 + S36 -> qAuto6) and h.map = (h1.map).(h2.map) }
pred S3toS3Auto6FIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Auto6[h] and Q.element =  qAuto1 + qAuto2 + qAuto3 + qAuto4 + qAuto5 + qAuto6 and Q.id = qAuto1 and Q.inv = (qAuto1 -> qAuto1 + qAuto2 -> qAuto2 + qAuto3 -> qAuto3 + qAuto4 -> qAuto4 + qAuto5 -> qAuto6 + qAuto6 -> qAuto5) and Q.mult = (qAuto1 -> qAuto1 -> qAuto1) + (qAuto1 -> qAuto2 -> qAuto2) + (qAuto1 -> qAuto3 -> qAuto3) + (qAuto1 -> qAuto4 -> qAuto4) + (qAuto1 -> qAuto5 -> qAuto5) + (qAuto1 -> qAuto6 -> qAuto6) + (qAuto2 -> qAuto1 -> qAuto2) + (qAuto2 -> qAuto2 -> qAuto1) + (qAuto2 -> qAuto3 -> qAuto5) + (qAuto2 -> qAuto4 -> qAuto6) + (qAuto2 -> qAuto5 -> qAuto3) + (qAuto2 -> qAuto6 -> qAuto4)+ (qAuto3 -> qAuto1 -> qAuto3) + (qAuto3 -> qAuto2 -> qAuto6) + (qAuto3 -> qAuto3 -> qAuto1) + (qAuto3 -> qAuto4 -> qAuto5) + (qAuto3 -> qAuto5 -> qAuto4) + (qAuto3 -> qAuto6 -> qAuto2)+ (qAuto4 -> qAuto1 -> qAuto4) + (qAuto4 -> qAuto2 -> qAuto5) + (qAuto4 -> qAuto3 -> qAuto6) + (qAuto4 -> qAuto4 -> qAuto1) + (qAuto4 -> qAuto5 -> qAuto2) + (qAuto4 -> qAuto6 -> qAuto3)+ (qAuto5 -> qAuto1 -> qAuto5) + (qAuto5 -> qAuto2 -> qAuto4) + (qAuto5 -> qAuto3 -> qAuto2) + (qAuto5 -> qAuto4 -> qAuto3) + (qAuto5 -> qAuto5 -> qAuto6) + (qAuto5 -> qAuto6 -> qAuto1)+ (qAuto6 -> qAuto1 -> qAuto6) + (qAuto6 -> qAuto2 -> qAuto3) + (qAuto6 -> qAuto3 -> qAuto4) + (qAuto6 -> qAuto4 -> qAuto2) + (qAuto6 -> qAuto5 -> qAuto1) + (qAuto6 -> qAuto6 -> qAuto5) and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h1.map = (S31 -> qAuto1 + S32 -> qAuto2 + S33 -> qAuto3 + S34 -> qAuto4 + S35 -> qAuto5 + S36 -> qAuto6) and h.map = (h1.map).(h2.map) }
//The following 4 predicates produce the unique commutative diagram for each strict homomorphism of S3
pred S3toS30HomFIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Hom0[h] and Q.element = q0Hom1 and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h.map = (h1.map).(h2.map) }
pred S3toS31HomFIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Hom1[h] and Q.element = q1Hom1 + q1Hom2 and Q.id = q1Hom1 and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h.map = (h1.map).(h2.map) }
pred S3toS32HomFIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Hom2[h] and Q.element = q1Hom1 + q1Hom2 and Q.id = q1Hom1 and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h.map = (h1.map).(h2.map) }
pred S3toS33HomFIT[h : Hom] {
	some disj h1, h2 : Hom | S3toS3Hom3[h] and Q.element = q1Hom1 + q1Hom2 and Q.id = q1Hom1 and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 and h.map = (h1.map).(h2.map) }

// Asserts that if we have a homomorphism from S3 to itself, then when we apply the First Isomorphism Theorem, we will obtain one of the 10 possible commutative diagrams
assert Main {
	all h : Hom | some disj h1, h2 : Hom | h.dom = S3 and h.ran = S3 and h1.dom = S3 and h1.ran = Q and h2.dom = Q and h2.ran = S3 implies (S3toS3Auto1FIT[h] or S3toS3Auto2FIT[h] or S3toS3Auto3FIT[h] or S3toS3Auto4FIT[h] or S3toS3Auto5FIT[h] or S3toS3Auto6FIT[h] or S3toS30HomFIT[h] or S3toS31HomFIT[h] or S3toS32HomFIT[h] or S3toS33HomFIT[h]) }




//run S3toS3Homs for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Auto1 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Auto2 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Auto3 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Auto4 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Auto5 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Auto6 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Hom0 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Hom1 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Hom2 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Hom3 for exactly 1 Hom, 10 Elements, exactly 1 Group
run S3toS3Auto1FIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS3Auto2FIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS3Auto3FIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS3Auto4FIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS3Auto5FIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS3Auto6FIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS30HomFIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS31HomFIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS32HomFIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
run S3toS33HomFIT for exactly 3 Hom, exactly 2 Elements, exactly 2 Group
