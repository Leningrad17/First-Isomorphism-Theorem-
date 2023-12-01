open util/integer
//Signatures used to represent a Group
sig Elements{}
sig Group {
	element : set Elements,
	mult : element -> element -> one element,
	id : one element,
	inv : element -> one element
	}
sig Hom {
	dom : one Group,
	ran : one Group,
	map :set Elements -> set Elements }



	


//Eliminates unnecessary elements from the instance window
pred CleanUp(e: Elements) {
	some g: Group | e in g.element }


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
fact {
	all e : Elements | CleanUp[e] }


//Claims that for every group, the identity element of a group will be its own inverse
assert IdentityIsOwnInverse{
	all g: Group | g.inv[g.id] = g.id }

//Claims that every element of a group has a unique inverse
assert EachElementHasUniqueInverse{
	all g: Group | all disj e1, e2: g.element | (g.inv[e1] not in g.inv[e2]) and (g.inv[e2] not in g.inv[e1])}

//fun Subgroups(g : Group) : Group {
	//{g2: Group | g2.element in g.element and g2.mult in g.mult and g2.id = g.id and g2.inv in g.inv} }

//pred IsASubgroupOf{
//	all g : Group | some g2 : Group-g| g2 in Subgroups[g] and g.mult not in g2.mult}

//Claims that the map relation of every homomorphism will only consider mappings from the elements of the domain of the homomorphism to the elements of the range of the homomorphism
fact {
	all h: Hom | all g : Elements | h.map[g] in h.ran.element and g in h.dom.element }

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

fun KernelGroups [h: Hom] : Elements {
	{ g: h.dom.element | h.map[g] = h.ran.id } }

fun TestGroup [h : Hom] : Group {
	{g : Group | } }

//pred SubgroupsofZ4 [g : Group] {
//	some disj e1, e2, e3, e4 : Elements | g.element = e1 + e2 + e3 + e4 and g.id = e1 and g.inv = (e1 -> e1) + (e2 -> e4) + (e3 -> e3) + (e4 -> e2) and g.mult = (e1 -> e1 -> e1) + (e1 -> e2 -> e2) + (e1 -> e3 -> e3) + (e1 -> e4 -> e4) + (e2 -> e1 -> e2) + (e2 -> e2 -> e3) + (e2 -> e3 -> e4) + (e2 -> e4 -> e1) + (e3 -> e1 -> e3) + (e3 -> e2 -> e4) + (e3 -> e3 -> e1) + (e3 -> e4 -> e2) + (e4 -> e1 -> e4) + (e4 -> e2 -> e1) + (e4 -> e3 -> e2) + (e4 -> e4 -> e3)
//	all g1 : Group-g | g1.element in g.element and rem[#(g.element),#(g1.element)] = 0 and g1.id = g.id}



 //Calculates the order of an element in a group
fun ElementOrder [g: Group, e: g.element] : Int {
		#(g.id.*(e.(g.mult))) }

//Asserts that for all elements of a group, the order of the elements will always divide the order of the group (i.e Lagrange's Theorem)
assert OrderofElementDividesGroupOrder {
	all g: Group | all e : g.element | rem[#(g.element),ElementOrder[g, e]] = 0 }







	

//pred Main{}

	



//Created Z/6Z for future testing purposes
pred CyclicGroupSize6 {
	some g: Group | some disj e1, e2, e3, e4, e5, e6 : Elements | g.element = e1 + e2 + e3 + e4 + e5 + e6
	and g.id = e1 and g.inv = (e2 -> e6 + e6 -> e2 + e3 -> e5 + e5 -> e3 + e4 -> e4 + e1 -> e1)
	and g.mult = ( e1 -> e1 -> e1 + e1 -> e2 -> e2 + e2 -> e1 -> e2 + e1 -> e3 -> e3 + e3 -> e1 -> e3 + e1 -> e4 -> e4 + e4 -> e1 -> e4 +  e1 -> e5 -> e5 + e5 -> e1 -> e5 + e1 -> e6 -> e6 + e6 -> e1 -> e6 + e2 -> e2 -> e3 + e2 -> e3 -> e4 + e3 -> e2 -> e4 + e2 -> e4 -> e5 + e4 -> e2 -> e5 + e2 -> e5 -> e6 + e5 -> e2 -> e6 + e2 -> e6 -> e1 + e6 -> e2 -> e1 + e3 -> e3 -> e5 + e3 -> e4 -> e6 + e4 -> e3 -> e6 + e3 -> e5 -> e1 + e5 -> e3 -> e1 + e3 -> e6 -> e2 + e6 -> e3 -> e2 + e4 -> e4 -> e1 + e4 -> e5 -> e2 + e5 -> e4 -> e2 + e4 -> e6 -> e3 + e6 -> e4 -> e3 + e5 -> e5 -> e3 + e5 -> e6 -> e4 + e6 -> e5 -> e4 + e6 -> e6 -> e5) }  


run HomsAreFunctions for exactly 2 Group, exactly 1 Hom, exactly 4 Elements
//run SubgroupsofZ4 for exactly 2 Group, 0 Hom, exactly 4 Elements
//run IsASubgroupOf for exactly 2 Group, exactly 1 Hom, exactly 5 Elements
//run Main for exactly 2 Group, exactly 1 Hom,  exactly 4 Elements
check IdentityIsOwnInverse for exactly 1 Group, 5 Elements
check EachElementHasUniqueInverse for exactly 1 Group, 5 Elements
check HomsMapIdentityToIdentity for exactly 2 Group, 1 Hom, exactly 5 Elements 
check HomMapofInverseEqualsInverseofHomMap for exactly 2 Group, 1 Hom, exactly 5 Elements
run CyclicGroupSize6 for exactly 1 Group, exactly 0 Hom, 7 Elements
check OrderofElementDividesGroupOrder for exactly 1 Group, exactly 0 Hom, 7 Elements






