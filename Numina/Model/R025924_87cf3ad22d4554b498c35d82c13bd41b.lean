import Mathlib

theorem inequalities_83463 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x + 2 * y = 1) :
    1 / x + 2 / y ≥ 25 / (1 + 48 * x * y ^ 2) := by
  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have h2 : x * y * (1 + 48 * x * y ^ 2) > 0 := by
    positivity
  have h3 : 1 / x + 2 / y - 25 / (1 + 48 * x * y ^ 2) ≥ 0 := by
    have h4 : (1 / x + 2 / y - 25 / (1 + 48 * x * y ^ 2)) = (y * (1 + 48 * x * y ^ 2) + 2 * x * (1 + 48 * x * y ^ 2) - 25 * x * y) / (x * y * (1 + 48 * x * y ^ 2)) := by
      field_simp
      <;> ring
    rw [h4]
    have h8 : y * (1 + 48 * x * y ^ 2) + 2 * x * (1 + 48 * x * y ^ 2) - 25 * x * y ≥ 0 := by
      have h9 : x = 1 - 2 * y := by linarith [h]
      rw [show x = 1 - 2 * y by linarith [h]]
      nlinarith [sq_nonneg (y - 1 / 4), sq_nonneg ((1 - 2 * y) * y), sq_nonneg ((1 - 2 * y) - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - 2 * y) - y), sq_nonneg ((1 - 2 * y) * ( (1 - 2 * y) - y)), mul_pos (show 0 < 1 - 2 * y by nlinarith) (show 0 < y by nlinarith), sq_nonneg ((1 - 2 * y) * (1 - 2 * y * 2)), sq_nonneg (y * 4 * (y - 1 / 2))]
    apply div_nonneg
    linarith
    all_goals nlinarith
  linarith