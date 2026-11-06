import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311864 (x y : ℝ) (hx : 0 ≤ x) (h : x^2 + (y - 2)^2 = 1)
  (W : ℝ) (hW : W = (3 * x^2 + 2 * sqrt 3 * x * y + 5 * y^2) / (x^2 + y^2)) :
  W ≥ 5 ∧ W ≤ 6 := by
  have h1 : x ^ 2 + y ^ 2 = 4 * y - 3 := by
    nlinarith
  have h2 : 0 < 4 * y - 3 := by
    nlinarith [sq_nonneg x, sq_nonneg (y - 2), sq_nonneg (y - 3 / 4)]
  have h01 : W ≥ 5 := by
    rw [hW]
    have eq1 : x ^ 2 + y ^ 2 = 4 * y - 3 := h1
    have h5_pos : 0 < x^2 + y ^ 2 := by nlinarith
    apply (le_div_iff₀ h5_pos).mpr
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      sq_nonneg (x - 0), sq_nonneg (y - 3), sq_nonneg (sqrt 3 * (x / 2) - (y - 3 / 2)), sq_nonneg (x - sqrt 3 * (y / 3)), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), sq_nonneg (x - sqrt 3 * (2 / 1) / 16), sq_nonneg ((y - 1) * 2), mul_nonneg (Real.sqrt_nonneg 3) (show 0 ≤ x by assumption)
    ]
  have h02 : W ≤ 6 := by
    rw [hW]
    have eq1 : x ^ 2 + y ^ 2 = 4 * y - 3 := h1
    have h5_pos : 0 < x^2 + y ^ 2 := by nlinarith
    apply (div_le_iff₀ h5_pos).mpr
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      sq_nonneg (sqrt 3 * x - y), sq_nonneg (sqrt 3 * (x) - (y * 0)), 
      sq_nonneg (x - sqrt 3 / 2), sq_nonneg (y - 3 / 2), sq_nonneg ((y - 2) * 10), sq_nonneg ((x - sqrt 3 / 2) * 10), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), sq_nonneg (y - 2)
    ]
  constructor
  · exact h01
  · exact h02