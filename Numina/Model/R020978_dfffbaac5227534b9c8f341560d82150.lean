import Mathlib

theorem algebra_296494 {a b c : ℝ} (h1 : a ≠ 0) (h2 : b ≠ 0) (h3 : c ≠ 0)
    (h4 : a + b + c = 0) (h5 : 1 / a + 1 / b + 1 / c = -4) :
    1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 = 16 := by 
  have eq1 : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 =
    (1 / a + 1 / b + 1 / c) ^ 2 - 2 * ( (1 / (a * b)) + (1 / (b * c)) + (1 / (c * a)) ) := by
    field_simp [h1, h2, h3]
    <;> ring
  have eq2 : (1 / (a * b)) + (1 / (b * c)) + (1 / (c * a)) = (a + b + c) / (a * b * c) := by 
    field_simp [h1, h2, h3]
    <;> ring
  have eq3 : (1 / (a * b)) + (1 / (b * c)) + (1 / (c * a)) = 0 := by
    rw [eq2]
    have h6 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact h1
      exact h2
      exact h3
    have h7 : a + b + c = 0 := h4
    simp [h7, h6]
  rw [eq1]
  rw [eq3]
  rw [h5]
  norm_num