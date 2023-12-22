open util/integer
open FirstIsoTheorem

//Creates cyclic group of order 6
pred CyclicGroupSize6 {
	some g: Group | some disj e1, e2, e3, e4, e5, e6 : Elements | g.element = e1 + e2 + e3 + e4 + e5 + e6
	and g.id = e1 and g.inv = (e2 -> e6 + e6 -> e2 + e3 -> e5 + e5 -> e3 + e4 -> e4 + e1 -> e1)
	and g.mult = ( e1 -> e1 -> e1 + e1 -> e2 -> e2 + e2 -> e1 -> e2 + e1 -> e3 -> e3 + e3 -> e1 -> e3 + e1 -> e4 -> e4 + e4 -> e1 -> e4 +  e1 -> e5 -> e5 + e5 -> e1 -> e5 + e1 -> e6 -> e6 + e6 -> e1 -> e6 + e2 -> e2 -> e3 + e2 -> e3 -> e4 + e3 -> e2 -> e4 + e2 -> e4 -> e5 + e4 -> e2 -> e5 + e2 -> e5 -> e6 + e5 -> e2 -> e6 + e2 -> e6 -> e1 + e6 -> e2 -> e1 + e3 -> e3 -> e5 + e3 -> e4 -> e6 + e4 -> e3 -> e6 + e3 -> e5 -> e1 + e5 -> e3 -> e1 + e3 -> e6 -> e2 + e6 -> e3 -> e2 + e4 -> e4 -> e1 + e4 -> e5 -> e2 + e5 -> e4 -> e2 + e4 -> e6 -> e3 + e6 -> e4 -> e3 + e5 -> e5 -> e3 + e5 -> e6 -> e4 + e6 -> e5 -> e4 + e6 -> e6 -> e5) }  


run CyclicGroupSize6 for exactly 1 Group, 0 Hom, 8 Elements
