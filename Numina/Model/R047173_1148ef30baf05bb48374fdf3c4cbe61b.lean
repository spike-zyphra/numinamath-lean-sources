import Mathlib

theorem algebra_11423 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^2 + 1 / x + 1 / y = 27 / 4) :
    15 / x - 3 / (4 * y) ≥ 6 := by
  have h1 : x ^ 3 * y + x * y ^ 3 + y + x = 27 / 4 * (x * y) := by 
    have hx' : x ≠ 0 := by linarith
    have hy' : y ≠ 0 := by linarith
    field_simp [hx', hy'] at h ⊢
    nlinarith [h, mul_pos hx hy]

  have h2 : 15 / x - 3 / (4 * y) - 6 ≥ 0 := by
    have h3 : 0 < x * y := mul_pos hx hy
    have h4 : 15 / x - 3 / (4 * y) - 6 = (60 * y - 3 * x - 24 * x * y) / (4 * x * y) := by
      field_simp
      <;> ring
    rw [h4] at *
    have h6 : 60 * y - 3 * x - 24 * x * y ≥ 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1 / 2), sq_nonneg (x - 2 * y), sq_nonneg (x * y - 1), sq_nonneg (x * y - 1 / 2), sq_nonneg (x - 2), sq_nonneg (y - 1 / 2), sq_nonneg (x * (y - 1 / 2)), sq_nonneg ((x - 2) * (y - 1 / 2)), h1, mul_pos hx hy]
    apply div_nonneg
    all_goals nlinarith [h6, mul_pos hx hy]
  linarith