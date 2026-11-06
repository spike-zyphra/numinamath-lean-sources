import Mathlib

theorem number_theory_24224 (x y:ℤ)(xpos: 0 < x)(ypos: 0 < y):
  (∀n:ℕ, 0 < n ∧ (2^n * y + 1) ∣ (x^(2^n) - 1)) → x = 1 := by 
  intro h 
  specialize h 0 
  norm_num at h 
  all_goals omega