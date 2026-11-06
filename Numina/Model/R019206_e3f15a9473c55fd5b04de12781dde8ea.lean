import Mathlib

open Real

theorem algebra_7411 : ¬∃ x, x < 0 ∧ (1 - 3 * x) / (x - 1) > 0 := by 
  rintro ⟨x, hx1, hx2⟩
  all_goals
    have h : x ≥ 0 := by
      omega
    omega