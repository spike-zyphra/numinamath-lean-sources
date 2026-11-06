import Mathlib

theorem number_theory_96768 :
    IsLeast {x | 0 < x ∧ ∃ k, k^2 = 360 * x} 40 ∧
    IsLeast {y | 0 < y ∧ ∃ m, m^3 = 360 * y} 45 → 40 + 45 = 85 := by 
  intro h
  norm_num