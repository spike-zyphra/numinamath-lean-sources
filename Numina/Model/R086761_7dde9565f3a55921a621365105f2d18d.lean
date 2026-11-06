import Mathlib

theorem number_theory_51041 (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : ∃ q : ℚ, (a * Real.sqrt 2 + b * Real.sqrt 3) / (b * Real.sqrt 2 + c * Real.sqrt 3) = q) :
    ∃ m : ℤ, ((a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c)) = m := by 
  use ((a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) : ℤ)
  all_goals norm_num