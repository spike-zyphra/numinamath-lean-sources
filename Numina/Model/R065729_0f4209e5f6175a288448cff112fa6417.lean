import Mathlib

theorem number_theory_282821 (U : ℕ) (h : 0 ≤ U ∧ U < 10) (h1 : 9 ∣ (20180 + U)) :
    (20180 + U) % 8 = 3 := by 
  have h2 : U = 7 := by
    omega
  subst h2
  norm_num