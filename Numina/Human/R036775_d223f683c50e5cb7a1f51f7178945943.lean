import Mathlib

theorem algebra_1274 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (h : ∃ k, 1 / x + 1 / y = k / (x + y)) :
    ∃ m, (x + y) ^ 2 = m * (x ^ 2 + y ^ 2) := by 
  use (x + y) ^ 2 / (x ^ 2 + y ^ 2)
  have : x ^ 2 + y ^ 2 ≠ 0 := by
    have hx2 : x ^ 2 > 0 := by
      exact sq_pos_of_ne_zero hx
    have hy2 : y ^ 2 > 0 := by
      exact sq_pos_of_ne_zero hy
    linarith
  field_simp