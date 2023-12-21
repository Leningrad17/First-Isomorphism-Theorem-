open lib/group[G] as G
open lib/group[H] as H

sig G {
	f : H
}

sig H {}

pred isHom[f : G -> H] {
	f[G/e] = H/e
	all g1, g2 : G | f[G/m[g1, g2]] = H/m[f[g1], f[g2]]
}

pred showIdentities {
	some g : G | g = G/e
	some h : H | h = H/e
}

pred showNonIdentities {
	some S : set G | all g : G | not g = G/e <=> g in S
	some S : set H | all g : H | not g = H/e <=> g in S
}

run Picture {
	isHom[f]
	showIdentities
//	showNonIdentities
} for exactly 4 G, 4 H
