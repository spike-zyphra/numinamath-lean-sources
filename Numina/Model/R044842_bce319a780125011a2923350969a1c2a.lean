import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_124869 (x y : ℝ) (h : (x - 3)^2 + 4 * (y - 1)^2 = 4) :
    (x + y - 3) / (x - y + 1) ≤ 1 ∧ (x + y - 3) / (x - y + 1) ≥ -1 := by
  have h1 : x - y + 1 ≠ 0 := by
    by_contra h1 
    have h2 : x - y + 1 = 0 := by linarith 
    nlinarith [sq_nonneg (x - y + 1), sq_nonneg (x + y - 3), sq_nonneg (x - 5), sq_nonneg (y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  constructor
  · -- Prove (x + y - 3) / (x - y + 1) ≤ 1
    have h2 : (x + y - 3) / (x - y + 1) ≤ 1 := by 
      by_cases h3 : (x - y + 1) > 0 
      · -- If x - y + 1 > 0, then multiply both sides by x - y + 1
        apply (div_le_iff₀ h3).mpr
        nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 3), sq_nonneg (x - y + 1), mul_self_nonneg (x - 3 - (y - 1) * 2), mul_self_nonneg (x - 5), mul_self_nonneg (y - 2), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1), h]
      by_cases h4 : (x - y + 1) < 0 
      · -- If x - y + 1 < 0, then multiply both sides by x - y + 1 and reverse inequality
        apply (div_le_iff_of_neg' h4).mpr
        nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 3), sq_nonneg (x - y + 1), mul_self_nonneg (x - 3 - (y - 1) * 2), mul_self_nonneg (x - 5), mul_self_nonneg (y - 2), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1), h]
      have h5 : x - y + 1 = 0 := by
        linarith 
      contradiction
    exact h2
  · -- Prove (x + y - 3) / (x - y + 1) ≥ -1
    have h2 : (x + y - 3) / (x - y + 1) ≥ -1 := by 
      by_cases h3 : (x - y + 1) > 0 
      · -- If x - y + 1 > 0, then multiply both sides by x - y + 1
        apply (le_div_iff₀ h3).mpr
        nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 3), sq_nonneg (x - y + 1), mul_self_nonneg (x - 3 - (y - 1) * 2), mul_self_nonneg (x - 5), mul_self_nonneg (y - 2), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1), h]
      by_cases h4 : (x - y + 1) < 0 
      · -- If x - y + 1 < 0, then multiply both sides by x - y + 1 and reverse inequality
        apply (le_div_iff_of_neg' h4).mpr
        nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 3), sq_nonneg (x - y + 1), mul_self_nonneg (x - 3 - (y - 1) * 2), mul_self_nonneg (x - 5), mul_self_nonneg (y - 2), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1), h]
      have h5 : x - y + 1 = 0 := by
        linarith 
      contradiction
    exact h2