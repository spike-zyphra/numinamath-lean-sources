import Mathlib

theorem number_theory_233217 : (4^4 : ℝ) > (2^6) ∧ (4^4 > 3^5) ∧ (4^4 > 5^3) ∧ (4^4 > 6^2) := by
  constructor
  norm_num
  constructor
  norm_num
  constructor
  norm_num
  norm_num