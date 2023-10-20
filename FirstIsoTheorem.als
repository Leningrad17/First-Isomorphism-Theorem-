
//Signatures used to represent a Group
sig Elements{
	Epairs : set Elements,
	Ebinop: Epairs -> set Elements}

sig Group {
	elements: set Elements,
	pairs : elements -> elements,
	binop : pairs -> elements
	}

//A map between our two signatures which allows for easier access to information on the internals
pred ElementsandGroupsCorrelate(g : Group) {
	all g : Group | Elements = g.elements and (all e1, e2: Elements | (e2 in e1.Epairs) iff (e1 -> e2 in g.pairs)) and (all e1, e2, e3: Elements | (e2 -> e3 in e1.Ebinop) iff (e1->e2->e3 in g.binop)) }

//Makes sure each group has at least one element and that all of the Elements displayed are in the group
pred GroupHasAtLeastOneElm(g: Group) {
	all g: Group | #g.elements > 0
	all e : Elements | e in g.elements }

//Makes sure that all possible pairings between elements exist (we want this since our binary operation must work on any two elements in our group
pred AllPossiblePairsExist(g : Group) {
	all g: Group | (g.elements->g.elements) = g.pairs}

//Enforces that our binary operation is well-defined by checking that every pair of points only maps to a singular element
pred EveryPairMapsToOneValueInElm(e : Elements) {
	all e: Elements | all e1 : Elements | e1 in e.Epairs implies (one e2 : Elements | e1 -> e2 in e.Ebinop)}

//Enforces that every group has a unique identity element, whose property is that whenever you apply the binary operation to it and any other
//element x, you return x.
pred EveryGroupHasIdentity(g : Group) {
	all g: Group | one i : Elements | all e1: Elements | (e1 -> e1 in i.Ebinop and i -> e1 in e1.Ebinop)}

	
	

pred GroupDefinition(g: Group) {
	all g: Group | GroupHasAtLeastOneElm[g]
	all g: Group | AllPossiblePairsExist[g]
	all g: Group | ElementsandGroupsCorrelate[g]
	all e : Elements | EveryPairMapsToOneValueInElm[e]
	all g: Group | EveryGroupHasIdentity[g]
	}





run GroupHasAtLeastOneElm for 3 Elements, exactly 1 Group
run GroupDefinition for 3 Elements, exactly 1 Group
