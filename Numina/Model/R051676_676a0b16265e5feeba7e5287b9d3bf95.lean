import Mathlib

theorem algebra_114361 : ∃ x y, x = 2 * 2 * 2 + 2 ∧ y = 2 * 2 * 2 + 2 ∧ 100 = x * y := by 
  refine ⟨2 * 2 * 2 + 2, 2 * 2 * 2 + 2, by rfl, by rfl, by norm_num⟩