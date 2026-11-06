import Mathlib

theorem algebra_14958 (a b c d : ℝ) (ha : a ≠ 0) (hroots : ∃ x y, x = 3 ∧ y = -2 ∧ a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ∧ a * y ^ 3 + b * y ^ 2 + c * y + d = 0) :
    (b + c) / a = -7 := by
  rcases hroots with ⟨x, y, hx1, hy1, hx2, hy2⟩
  rw [hx1] at hx2
  rw [hy1] at hy2
  have eq1 : a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 0 := by linarith
  have eq2 : a * (-2) ^ 3 + b * (-2) ^ 2 + c * (-2) + d = 0 := by linarith
  have eq3 : b + c = -7 * a := by
    linarith
  field_simp [ha]
  <;> linarith [eq3]