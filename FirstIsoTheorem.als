
//Signatures used to represent a Group
sig Elements{}
sig Group {
	element : set Elements,
	mult : element -> element -> one element,
	id : one element,
	inv : element -> one element
	}

	


//Makes sure that all of the elements displayed are in the group
pred GroupHasAtLeastOneElm(g: Group) {
	all g: Group | g.element = Elements }


//Enforces the property that whenever you apply the binary operation to the identity element and any other element (which
//can include the identity as well), you return the other element (i.e., given a binary operation "x" and an arbitrary element e,
// e x id = e and id x e = e)
pred IdentityBinOpProperty(g : Group) {
	all g: Group | all e1 : g.element | (e1 -> e1 in g.mult[g.id]) and (g.id -> e1 in g.mult[e1]) }

//Enforces the property that the identity element of a group will be its own inverse
pred IdentityIsOwnInverse(g : Group) {
	all g: Group | g.inv[g.id] = g.id }

//Enforces the property that every element of a group will have a unique inverse
pred EachElementHasUniqueInverse(g: Group) {
	all g: Group | all disj e1, e2: g.element | (g.inv[e1] not in g.inv[e2]) and (g.inv[e2] not in g.inv[e1])}

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
	all g: Group | GroupHasAtLeastOneElm[g]
	all g: Group | IdentityBinOpProperty[g]
	all g: Group | IdentityIsOwnInverse[g]
	all g: Group | EachElementHasUniqueInverse[g]
	all g: Group | InverseBinOpProperty[g]
	all g: Group | AssociativityBinOpProperty[g]
	}


run GroupDefinition for exactly 1 Group, exactly 5 Elements



