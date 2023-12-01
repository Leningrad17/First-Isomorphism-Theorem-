open util/integer
open FirstIsoTheorem

//Creates the direct product of the cyclic group of order 2 and the cyclic group of order 2
pred DirectProductC2andC2(g: Group) {
	all g: Group | some disj e1, e2, e3, e4 : Elements | g.element = e1+ e2 + e3 + e4 and g.id = e1
	and g.inv = (e1 -> e1) + (e2 -> e2) + (e3 -> e3) + (e4 -> e4) and g.mult = (e1 -> e1 -> e1) + (e1 -> e2 -> e2) + (e1 -> e3 -> e3) + (e1 -> e4 -> e4) + (e2 -> e1 -> e2) + (e2 -> e2 -> e1) + (e2 -> e3 -> e4) + (e2 -> e4 -> e3) + (e3 -> e1 -> e3) + (e3 -> e2 -> e4) + (e3 -> e3 -> e1) + (e3 -> e4 -> e2) + (e4 -> e1 -> e4) + (e4 -> e2 -> e3) + (e4 -> e3 -> e2) + (e4 -> e4 -> e1) }
//Asserts that none of the elements of C2xC2 are of order 4 (meaning it is not cyclic)
assert NoElementofOrder4 {
	all g : Group | DirectProductC2andC2[g] implies (no e : g.element | div[#(g.element),ElementOrder[g,e]] = 1) }

run DirectProductC2andC2 for exactly 1 Group, 0 Hom, 8 Elements
check NoElementofOrder4 for exactly 1 Group, 0 Hom, 8 Elements
