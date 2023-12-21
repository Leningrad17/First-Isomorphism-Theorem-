pred isGroup[A : set univ, m : A -> A -> A, e : A , i : A -> A] {
	// associative law
	all a1, a2, a3 : A | m[a1, m[a2, a3]] = m[m[a1, a2], a3]
	// unit laws
	all a : A | m[e, a] = a
	all a : A | m[a, e] = a
	// inverse laws
	all a : A | m[i[a], a] = e
	all a : A | m[a, i[a]] = e
}

pred isHom[A1 : set univ, m1 : A1 -> A1 -> A1, e1 : A1,
		   A2 : set univ, m2 : A2 -> A2 -> A2, e2 : A2,
			f : A1 -> A2] {
	all a1, a2 : A1 | f[m1[a1, a2]] = m2[f[a1], f[a2]]
	f[e1] = e2
}

sig G {
	G_m : G -> G,
	G_i : G,
	f : H
}
one sig G_e extends G {}

sig H {
	H_m : H -> H,
	H_i : H
}
one sig H_e extends H {}

fact {
	isGroup[G, G_m, G_e, G_i]
	isGroup[H, H_m, H_e, H_i]
	isHom[G, G_m, G_e, H, H_m, H_e, f]
}

pred showKernel {
	some K : set G | K = f.H_e
}

run showKernel for exactly 4 G, exactly 4 H
