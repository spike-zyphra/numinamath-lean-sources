import Mathlib

theorem number_theory_206874 {A B C : ℤ}
    (hA : A = 177^5 + 30621 * 173^3 - 173^5)
    (hB : B = 173^5 + 30621 * 177^3 - 177^5)
    (hC : C = 173^4 + 30621^2 + 177^4) :
    Int.gcd A C = 30637 ∧ Int.gcd B C = 30637 := by 
  rw [hA, hB, hC]
  constructor
  · -- Show that the GCD of A and C is 30637
    norm_num [Int.gcd]
  · -- Show that the GCD of B and C is 30637
    norm_num [Int.gcd]