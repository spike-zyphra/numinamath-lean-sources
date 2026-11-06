import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_167245 {x : ℝ} (hx : x ≠ 0) :
    cos (π / x) = -x^6 - 4 * x^5 + 2 * x^4 + 12 * x^3 - 9 * x^2 - 1 ↔ x = 1 := by
  constructor
  · -- Assume cos (π / x) = -x^6 - 4 * x^5 + 2 * x^4 + 12 * x^3 - 9 * x^2 - 1, prove x = 1
    intro h_eq
    have h1 : -1 ≤ cos (π / x) := by
      apply Real.neg_one_le_cos
    have h2 : cos (π / x) ≤ 1 := by
      apply Real.cos_le_one
    have h3 : -1 ≤ -x^6 - 4 * x^5 + 2 * x^4 + 12 * x^3 - 9 * x^2 - 1 := by
      have h4 : cos (π / x) = -x^6 - 4 * x^5 + 2 * x^4 + 12 * x^3 - 9 * x^2 - 1 := h_eq
      nlinarith [h4, h1, h2]
    have h4 : -x^6 - 4 * x^5 + 2 * x^4 + 12 * x^3 - 9 * x^2 - 1 ≤ 1 := by
      have h5 : cos (π / x) = -x^6 - 4 * x^5 + 2 * x^4 + 12 * x^3 - 9 * x^2 - 1 := h_eq
      nlinarith [h5, h1, h2]
    have h5 : x^2 * (x + 3)^2 * (x - 1)^2 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 2 - 3), sq_nonneg (x * (x + 1)), sq_nonneg ((x * x) - (x * 1)), sq_nonneg ((x - 1) * x + (x + 1)), sq_nonneg ((x + 3) ^ 2), sq_nonneg ((x - 1) ^ 2), sq_pos_of_ne_zero (show x ^ 2 ≠ 0 by intro h; apply hx; nlinarith), sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg ((x - 1) ^ 3)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    cases' (mul_eq_zero.mp h6) with h8 h9
    · -- Case x^2 = 0
      have h10 : x^2 = 0 := by
        nlinarith
      have h11 : x = 0 := by
        nlinarith
      contradiction
    · -- Case (x + 3)^2 = 0
      have h10 : (x + 3) ^ 2 = 0 := by
        nlinarith
      have h11 : x + 3 = 0 := by
        apply pow_eq_zero 
        exact h10
      have h12 : x = -3 := by
        linarith
      have hcos : cos (π / x) = -1 := by 
        rw [h_eq]
        rw [show x = -3 by linarith]
        norm_num
      have hcos_pi : cos (π / (x)) = 0.5 := by
        rw [show x = -3 by linarith]
        have h1 : π / (-3 : ℝ) = - (π / 3) := by ring
        rw [h1]
        have h4 : cos (- (π / 3) ) = cos (π / 3) := by
          rw [cos_neg]
        rw [h4]
        rw [cos_pi_div_three]
        all_goals norm_num
      rw [hcos_pi] at hcos
      all_goals nlinarith
    · -- Case (x - 1)^2 = 0
      have h10 : (x - 1) ^ 2 = 0 := by
        nlinarith
      have h11 : x - 1 = 0 := by
        apply pow_eq_zero 
        exact h10
      linarith
  · -- Assume x = 1, prove cos (π / x) = -x^6 - 4 * x^5 + 2 * x^4 + 12 * x^3 - 9 * x^2 - 1
    intro h_eq
    rw [h_eq]
    have h1 : cos (π / (1 : ℝ)) = -1 := by
      have h2 : π / (1 : ℝ) = π := by 
        ring
      rw [h2]
      rw [Real.cos_pi]
    rw [h1]
    all_goals norm_num