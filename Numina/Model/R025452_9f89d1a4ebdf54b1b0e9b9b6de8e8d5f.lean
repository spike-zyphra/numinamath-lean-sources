import Mathlib

theorem algebra_215888 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : 1 / a - 1 / b = 1 / (a + b)) :
    1 / a ^ 2 - 1 / b ^ 2 = 1 / (a * b) := by
  have h1 : a + b ≠ 0 := by 
    by_contra h2
    have h2' : a + b = 0 := by linarith
    rw [h2'] at h 
    field_simp [(show a ≠ 0 by exact ha), (show b ≠ 0 by exact hb)] at h ⊢ 
    <;> nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb)]
  have eq2 : b ^ 2 - a ^ 2 = a * b := by 
    field_simp [(show a ≠ 0 by exact ha), (show b ≠ 0 by exact hb), (show a + b ≠ 0 by exact h1)] at h ⊢
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show a + b ≠ 0 by exact h1)]
  have eq3 : 1 / a ^ 2 - 1 / b ^ 2 = (b ^ 2 - a ^ 2) / (a ^ 2 * b ^ 2) := by
    have h2' : a ≠ 0 := ha
    have h3' : b ≠ 0 := hb
    field_simp [(show a ≠ 0 by exact ha), (show b ≠ 0 by exact hb)]
    <;> ring
  rw [eq3]
  rw [eq2]
  have h2' : a * b ≠ 0 := mul_ne_zero (show a ≠ 0 by exact ha) (show b ≠ 0 by exact hb)
  field_simp [(show a * b ≠ 0 by exact h2'), (show a ≠ 0 by exact ha), (show b ≠ 0 by exact hb)]
  <;> nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_pos_of_ne_zero (show a + b ≠ 0 by exact h1), sq_nonneg (a * b), sq_nonneg (a + b)]