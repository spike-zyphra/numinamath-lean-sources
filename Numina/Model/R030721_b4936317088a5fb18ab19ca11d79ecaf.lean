import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_282765 (x y a b : ℝ)
  (h₁ : x^2 + y^2 ≤ 1) (h₂ : a^2 + b^2 ≤ 2) :
  |b * (x^2 - y^2) + 2 * a * x * y| ≤ sqrt 2 := by
  have h3 : (b * (x^2 - y^2) + 2 * a * x * y)^2 ≤ 2 := by
    have h4 : (b * (x^2 - y^2) + 2 * a * x * y)^2 ≤ (a^2 + b^2) * ((x^2 - y^2)^2 + (2 * x * y)^2) := by
      nlinarith [sq_nonneg (b * (x^2 - y^2) - a * (2 * x * y)), sq_nonneg (a * (x^2 - y^2) - b * (2 * x * y))]
    have h5 : (x^2 - y^2)^2 + (2 * x * y)^2 = (x^2 + y^2)^2 := by
      ring_nf
    have h6 : (x^2 + y^2)^2 ≤ 1 := by
      nlinarith [sq_nonneg (x^2 + y^2 - 1)]
    have h7 : (x^2 - y^2)^2 + (2 * x * y)^2 ≤ 1 := by
      have h8 : (x^2 - y^2)^2 + (2 * x * y)^2 = (x^2 + y^2)^2 := by
        ring_nf
      nlinarith [h8, h6]
    nlinarith [h4, h7, h₂]
  have h4 : |b * (x^2 - y^2) + 2 * a * x * y| ≤ Real.sqrt 2 := by
    have h5 : (b * (x^2 - y^2) + 2 * a * x * y)^2 ≤ 2 := h3
    have h6 : |b * (x^2 - y^2) + 2 * a * x * y| = Real.sqrt ((b * (x^2 - y^2) + 2 * a * x * y)^2) := by
      rw [Real.sqrt_sq_eq_abs]
    have h7 : Real.sqrt ((b * (x^2 - y^2) + 2 * a * x * y)^2) ≤ Real.sqrt (2 : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
    have h8 : Real.sqrt (2 : ℝ) = Real.sqrt 2 := by
      norm_num
    linarith [h6, h7, h8]
  simpa using h4