import Mathlib

open Real Set

theorem algebra_324499 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^2 + 1 / x + 1 / y = 27 / 4) :
    15 / x - 3 / (4 * y) ≥ 6 := by
  have h2 : x ^ 3 * y + x * y ^ 3 + x + y = 27 / 4 * (x * y) := by
    have eq1 : x ^ 2 + y ^ 2 + 1 / x + 1 / y = 27 / 4 := by
      linarith
    field_simp [hx, hy, mul_pos hx hy] at eq1 ⊢
    nlinarith [mul_pos hx hy, sq_nonneg (x - 2), sq_nonneg (y - 1 / 2), sq_nonneg (x * y -1)]
  have eq2 : 15 / x - 3 / (4 * y) = (15 * y - 3 / 4 * x) / (x * y) := by
    field_simp [show 0 < x by linarith, show 0 < y by linarith, show 0 < (x * y) by nlinarith]
    <;> ring
  have eq3 : 15 * y - 3 / 4 * x ≥ 6 * (x * y) := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1 / 2), sq_nonneg (x * y -1), h2, mul_pos hx hy, sq_nonneg (x - 2 * y), sq_nonneg (x * y -1), mul_pos hx hy]
  have eq4 : 15 / x - 3 / (4 * y) ≥ 6 := by
    have pos1 : 0 < x * y := mul_pos hx hy
    have eq5 : (15 * y - 3 / 4 * x) / (x * y) ≥ 6 := by
      have h3 : 15 * y - 3 / 4 * x ≥ 6 * (x * y) := eq3
      have h4 : (15 * y - 3 / 4 * x) / (x * y) ≥ 6 := by
        have pos1 : 0 < x * y := mul_pos hx hy
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith
      exact h4
    nlinarith [eq2, eq5]
  linarith