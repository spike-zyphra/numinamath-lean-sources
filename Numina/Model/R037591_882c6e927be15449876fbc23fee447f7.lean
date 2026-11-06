import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311855 (x y : ℝ) (hx : 0 < y) (hy : y < x) (hxy : x * y = 1) :
    2 * sqrt 2 ≤ (x ^ 2 + y ^ 2) / (x - y) := by 
  have h1 : x - y > 0 := by linarith
  have h2 : x ^ 2 + y ^ 2 = (x - y) ^ 2 + 2 := by
    nlinarith [hxy]
  have h3 : (x ^ 2 + y ^ 2) / (x - y) = (x - y) + 2 / (x - y) := by
    have h4 : x - y > 0 := h1
    rw [h2]
    field_simp
    <;> ring
  rw [h3]
  have h4 : (x - y) + 2 / (x - y) ≥ 2 * Real.sqrt 2 := by
    have h5 : (x - y) * (2 / (x - y)) = 2 := by
      field_simp [h1]
      <;> nlinarith
    have h6 : ((x - y) + 2 / (x - y)) - 2 * Real.sqrt 2 ≥ 0 := by
      have h7 : 0 < (x - y : ℝ) := h1
      have h8 : ((x - y) + 2 / (x - y)) - 2 * Real.sqrt 2 =
          ((x - y) ^ 2 + 2 - 2 * Real.sqrt 2 * (x - y)) / (x - y) := by
        field_simp [h7]
        <;> ring
      rw [h8] at *
      apply div_nonneg
      · -- Show that the numerator is non-negative
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg ((x - y) - Real.sqrt 2)]
      · -- Show that the denominator is non-negative
        nlinarith
    linarith
  linarith [h4, Real.sqrt_nonneg 2]