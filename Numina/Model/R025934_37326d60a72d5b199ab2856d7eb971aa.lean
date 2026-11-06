import Mathlib

noncomputable def star (a b : ℝ) := a ^ 2 + 2 * a * b + b ^ 2

theorem algebra_12157 {a b : ℝ} (ha : a = 4) (hb : b = 6) : star a b = 100 := by 
  rw [show star a b = a ^ 2 + 2 * a * b + b ^ 2 by rfl]
  rw [ha, hb]
  norm_num