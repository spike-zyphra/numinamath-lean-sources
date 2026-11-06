import Mathlib

theorem algebra_2742 {a b : ℝ} (hab : a = 3 ∧ b = 1 / 3) : a / b = 9 := by
  rcases hab with ⟨ha, hb⟩
  rw [ha, hb]
  norm_num