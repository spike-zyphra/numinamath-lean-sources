import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_151180 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (h : 19/x + 98/y = 1) :
  x + y ≥ 117 + 14*sqrt 38 := by
  have h1 : x * y = 19 * y + 98 * x := by
    field_simp at h
    nlinarith
  have h2 : (x - 19) * (y - 98) = 1862 := by
    nlinarith [h1]
  have hx2 : x ≥ 19 := by
    by_contra h4
    push_neg at h4
    have h5 : 19 / x + 98 / y > 1 := by
      have hx6 : x > 0 := by linarith
      have hx7 : y > 0 := by linarith
      have hx8 : 19 / x > 1 := by
        have hx9 : x < (19 : ℝ) := by linarith
        have hx10 : 19 / x > 1 := by
          apply (lt_div_iff' (by linarith)).mpr
          nlinarith
        linarith
      have hx11 : 98 / y > 0 := by
        apply div_pos
        linarith
        linarith
      linarith
    linarith
  have hy2 : y ≥ 98 := by
    by_contra h4
    push_neg at h4
    have h5 : 19 / x + 98 / y > 1 := by
      have hx6 : x > 0 := by linarith
      have hx7 : y > 0 := by linarith
      have hx8 : 19 / x > 0 := by
        apply div_pos
        linarith
        linarith
      have hx11 : 98 / y > 1 := by
        have hx9 : y < (98 : ℝ) := by linarith
        have hx10 : 98 / y > 1 := by
          apply (lt_div_iff' (by linarith)).mpr
          nlinarith
        linarith
      linarith
    linarith
  have h7 : (x - 19) + (y - 98) ≥ 14 * Real.sqrt 38 := by
    nlinarith [sq_nonneg ((x - 19) - 7 * Real.sqrt 38), sq_nonneg ((y - 98) - 7 * Real.sqrt 38),
      Real.sqrt_nonneg 38, Real.sq_sqrt (show 0 ≤ (38 : ℝ) by norm_num),
      mul_nonneg (Real.sqrt_nonneg 38) (Real.sqrt_nonneg 38)]
  have h3 : x + y = (x - 19) + (y - 98) + 117 := by
    linarith
  linarith [h3, h7]