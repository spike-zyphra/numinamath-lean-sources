import Mathlib.Tactic

open Real

theorem inequalities_115356 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^2 + 8 / (x * y) + y^2 ≥ 8 := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : x^2 + 8 / (x * y) + y^2 ≥ 8 := by
    have h3 : x^2 + 8 / (x * y) + y^2 - 8 ≥ 0 := by
      have h4 : (x ^ 2 + 8 / (x * y) + y ^ 2 - 8) = (x ^ 3 * y + y ^ 3 * x + 8 - 8 * (x * y)) / (x * y) := by
        field_simp
        ring
      rw [h4]
      have h5 : x ^ 3 * y + y ^ 3 * x + 8 - 8 * (x * y) ≥ 0 := by
        nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - 2), sq_nonneg (x * y - (x ^ 2 + y ^ 2)/2), sq_nonneg (x - y), sq_nonneg (x * y - (x ^ 2 + y ^ 2)/2), sq_nonneg (x * y - 2)]
      have h6 : (x ^ 3 * y + y ^ 3 * x + 8 - 8 * (x * y)) / (x * y) ≥ 0 := by
        apply div_nonneg h5 (by positivity)
      linarith
    linarith
  linarith