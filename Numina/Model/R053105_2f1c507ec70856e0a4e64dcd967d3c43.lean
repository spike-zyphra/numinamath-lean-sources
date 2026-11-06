import Mathlib

open Real
open scoped BigOperators

theorem inequalities_226453 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hc : 0 < c) (h : a^2 + b^2 = c^2) :
  (a + b) / sqrt 2 ≤ c := by
  have h1 : (a + b) ^ 2 ≤ 2 * (a^2 + b^2) := by
    nlinarith [sq_nonneg (a - b)]
  have h2 : (a + b) ^ 2 ≤ 2 * c^2 := by
    have h3 : a^2 + b^2 = c^2 := h
    nlinarith [h1, h3]
  have h4 : (a + b) / Real.sqrt 2 ≤ c := by
    have h5 : Real.sqrt 2 > 0 := by positivity
    have h6 : a + b ≤ c * Real.sqrt 2 := by
      have h7 : (c * Real.sqrt 2) ^ 2 = c^2 * (Real.sqrt 2)^2 := by ring
      have h8 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h10 : (a + b) ^ 2 ≤ (c * Real.sqrt 2) ^ 2 := by
        rw [h7, h8]
        nlinarith [h2]
      nlinarith [sq_nonneg (a + b - c * Real.sqrt 2), sq_nonneg (c * Real.sqrt 2 - (a + b)), h10, mul_nonneg (show 0 ≤ (c : ℝ) by nlinarith) (show 0 ≤ Real.sqrt 2 by positivity), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
    have h7 : Real.sqrt 2 > 0 := by positivity
    have h8 : (a + b) / Real.sqrt 2 ≤ c := by
      apply (div_le_iff₀ h7).mpr
      nlinarith
    linarith
  exact h4