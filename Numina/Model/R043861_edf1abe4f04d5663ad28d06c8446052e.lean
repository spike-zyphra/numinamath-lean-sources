import Mathlib

theorem algebra_158937 {a : PNat → ℤ} (apos : ∀ n, 0 < a n)
  (ainc : ∀ n, a n < a (n + 1))
  (ha : ∀ n, a (n + 2) = a (n + 1) + a n)
  (a7eq : a 7 = 120) : a 8 = 194 := by
  have h1 : a 1 > 0 := apos 1
  have h2 : a 2 > 0 := apos 2
  have h3 : a 3 > 0 := apos 3
  have h4 : a 4 > 0 := apos 4
  have h5 : a 5 > 0 := apos 5
  have h6 : a 6 > 0 := apos 6
  have h7 : a 7 > 0 := apos 7
  have h8 : a 8 > 0 := apos 8
  have h9 : a 1 < a 2 := ainc 1
  have h10 : a 2 < a 3 := ainc 2
  have h11 : a 3 < a 4 := ainc 3
  have h12 : a 4 < a 5 := ainc 4
  have h13 : a 5 < a 6 := ainc 5
  have h14 : a 6 < a 7 := ainc 6
  have h15 : a 7 < a 8 := ainc 7
  have eq1 : a 3 = a 2 + a 1 := by
    specialize ha 1
    simpa using ha
  have eq2 : a 4 = a 3 + a 2 := by
    specialize ha 2
    simpa using ha
  have eq3 : a 5 = a 4 + a 3 := by
    specialize ha 3
    simpa using ha
  have eq4 : a 6 = a 5 + a 4 := by
    specialize ha 4
    simpa using ha
  have eq5 : a 7 = a 6 + a 5 := by
    specialize ha 5
    simpa using ha
  have eq6 : a 8 = a 7 + a 6 := by
    specialize ha 6
    simpa using ha
  omega