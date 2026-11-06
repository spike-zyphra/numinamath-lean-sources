import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_9144 (a : ℝ) :
  (∀ x > 0, deriv (λ x => log x - a * (x - 1) / (x + 1)) x ≥ 0) ↔ a ≤ 2 := by
  constructor
  · -- Assume that for all x > 0, the derivative is non-negative.
    intro h
    have h1 := h 1 (by norm_num)
    simp [deriv_sub, deriv_div, deriv_log, deriv_id'', div_eq_mul_inv, mul_comm a, mul_assoc] at h1
    norm_num at h1
    nlinarith
  · -- Assume a ≤ 2, prove that the derivative is non-negative for all x > 0.
    intro ha x hx
    have h1 : deriv (λ x => log x - a * (x - 1) / (x + 1)) x = 1 / x - (2 * a) / (x + 1) ^ 2 := by
      simp [deriv_sub, deriv_div, deriv_log, deriv_id'', mul_comm a, mul_assoc]
      field_simp [(show x ≠ 0 by linarith), (show x + 1 ≠ 0 by linarith)]
      ring
    rw [h1]
    have h3 : x > 0 := hx
    have h4 : x + 1 > 0 := by
      linarith
    have h5 : (1 / x - (2 * a) / (x + 1) ^ 2) = ((x + 1) ^ 2 - 2 * a * x) / (x * (x + 1) ^ 2) := by
      field_simp [(show x ≠ 0 by linarith), (show x + 1 ≠ 0 by linarith)]
      ring
    rw [h5]
    have h6 : x * (x + 1) ^ 2 > 0 := by
      positivity
    have h7 : (x + 1) ^ 2 - 2 * a * x ≥ 0 := by
      nlinarith [sq_nonneg (x - (a - 1)), sq_nonneg (x - 1), sq_nonneg (a - 2), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (a), mul_pos hx (show 0 < x + 1 by linarith)]
    apply div_nonneg
    · linarith
    · positivity