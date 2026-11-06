import Mathlib

  theorem algebra_310625 (a b : ℚ)  (ha : a = 1 / 2 ∨ a = 1 / 4 ∨ a = 1 / 6 ∨ a = 1 / 8 ∨ a = 1 / 10 ∨ a = 1 / 12) (hb : b = 1 / 2 ∨ b = 1 / 4 ∨ b = 1 / 6 ∨ b = 1 / 8 ∨ b = 1 / 10 ∨ b = 1 / 12 ) (hs : ∑ x in {1 / 2, 1 / 4, 1 / 6, 1 / 8, 1 / 10, 1 / 12}, x - a - b = 1) (hab : a > b) :
  a = 1 / 8 ∧ b = 1 / 10 := by
  norm_num [Finset.sum_insert, Finset.sum_singleton] at hs
  rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl) <;> rcases hb with (rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num at hs hab <;> tauto