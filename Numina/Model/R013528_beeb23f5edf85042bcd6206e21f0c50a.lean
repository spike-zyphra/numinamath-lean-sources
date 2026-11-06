import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_107241 (x y a b : ℝ)
  (h₀ : x^2 + y^2 ≤ 1) (h₁ : a^2 + b^2 ≤ 2) :
  |b * (x^2 - y^2) + 2 * a * x * y| ≤ sqrt 2 := by
  have h2 : (b * (x^2 - y^2) + 2 * a * x * y ) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (a * (x ^ 2 - y ^ 2) - b * (2 * x * y)), 
          sq_nonneg (a * (2 * x * y) - b * (x ^ 2 - y ^ 2)), 
          sq_nonneg (x^2 + y^2 - 1), 
          sq_nonneg (a^2 + b^2 - 2), 
          sq_nonneg ((2 * x * y) ^ 2 - (x ^ 2 - y ^ 2) ^ 2), 
          sq_nonneg (x ^ 2 - y ^ 2 - 2 * x * y), 
          h₀, h₁, mul_nonneg (show (0 : ℝ) ≤ 1 - (x ^ 2 + y ^ 2) by nlinarith) (show (0 : ℝ) ≤ 1 - (x ^ 2 + y ^ 2) by nlinarith)]
  have h3 : |b * (x^2 - y^2) + 2 * a * x * y| ≤ Real.sqrt 2 := by
    have h2' : (b * (x^2 - y^2) + 2 * a * x * y) ^ 2 ≤ (2 : ℝ) := h2
    have h4 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have h5 : |b * (x^2 - y^2) + 2 * a * x * y| = Real.sqrt ((b * (x^2 - y^2) + 2 * a * x * y) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h5]
    have h6 : Real.sqrt ((b * (x^2 - y^2) + 2 * a * x * y) ^ 2) ≤ Real.sqrt ((2 : ℝ)) := by
      apply Real.sqrt_le_sqrt
      linarith
    nlinarith [Real.sqrt_nonneg 2]
  exact h3