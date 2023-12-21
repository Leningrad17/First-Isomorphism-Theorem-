module group[elem]

private one sig Group {
	mult : elem -> elem -> one elem,
	id : one elem,
	inv : elem -> one elem
}
{
	// associative law
	all g1, g2, g3 : elem | mult[g1, mult[g2, g3]] = mult[mult[g1, g2], g3]
	// unit laws
	all g : elem | m[e, g] = g
	all g : elem | m[g, e] = g
	// inverse laws
	all g : elem | m[i[g], g] = e
	all g : elem | m[g, i[g]] = e
}

fun m : elem -> elem -> elem { Group.mult }
fun e : elem { Group.id }
fun i : elem -> elem { Group.inv }
