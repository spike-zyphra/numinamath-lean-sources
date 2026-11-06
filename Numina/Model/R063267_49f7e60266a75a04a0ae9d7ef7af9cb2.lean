import Mathlib

theorem algebra_95244 (x : ℝ) (hx : x ≠ 0) :
    Real.sqrt (1 + (x ^ 4 - 1) ^ 2 / (2 * x ^ 2) ^ 2) =
    x ^ 2 / 2 + 1 / (2 * x ^ 2) := by
  have h1 : (1 + (x ^ 4 - 1) ^ 2 / (2 * x ^ 2) ^ 2) = ((x ^ 4 + 1) / (2 * x ^ 2)) ^ 2 := by
    field_simp
    ring_nf
  rw [h1]
  -- square root of a square is a
  have h2 : 0 < (x ^ 4 + 1) / (2 * x ^ 2) := by
    have hx2_pos : 0 < x ^ 2 := by
      apply sq_pos_of_ne_zero
      exact hx
    have hx4_pos : 0 < x ^ 4 := by
      have h1 : x ^ 2 > 0 := by apply sq_pos_of_ne_zero; exact hx
      nlinarith [sq_nonneg x]
    have h_pos : 0 < x^4 + 1 := by linarith [hx4_pos]
    apply div_pos
    linarith
    positivity
  have h3 : Real.sqrt (((x ^ 4 + 1) / (2 * x ^ 2)) ^ 2) = (x ^ 4 + 1) / (2 * x ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_pos h2]
    all_goals norm_num
  rw [h3]
  -- to show algebra is same
  field_simp
  <;> ring_nf <;> field_simp
  <;> nlinarith