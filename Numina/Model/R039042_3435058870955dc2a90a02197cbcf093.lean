import Mathlib

open Real

theorem inequalities_284184 (a b c : ℝ) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    a + b + c < sqrt (3 * (a^2 + b^2 + c^2)) := by
  have h1 : (a + b + c) ^ 2 < 3 * (a^2 + b^2 + c^2) := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by intro h'; apply h.1; linarith),
      sq_pos_of_ne_zero (show a - c ≠ 0 by intro h'; apply h.2.1; linarith),
      sq_pos_of_ne_zero (show b - c ≠ 0 by intro h'; apply h.2.2; linarith)
      ]
  by_cases h_nonneg : a + b + c ≥ 0
  · -- Case where a + b + c ≥ 0.
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (3 * (a ^ 2 + b ^ 2 + c ^ 2)) := Real.sqrt_nonneg _
    have h_sq : (a + b + c) ^ 2 < (Real.sqrt (3 * (a ^ 2 + b ^ 2 + c ^ 2))) ^ 2 := by
      have h_sqrt_sq : (Real.sqrt (3 * (a ^ 2 + b ^ 2 + c ^ 2)) ) ^ 2 = 3 * (a ^ 2 + b ^ 2 + c ^ 2) := Real.sq_sqrt (by positivity)
      nlinarith [Real.sqrt_nonneg (3 * (a ^ 2 + b ^ 2 + c ^ 2)), h1, h_sqrt_sq]
    have h_lt_sqrt : a + b + c < Real.sqrt (3 * (a^2 + b^2 + c^2)) := by
      nlinarith [Real.sqrt_nonneg (3 * (a^2 + b^2 + c^2)), h_nonneg, Real.sq_sqrt (show 0 ≤ 3 * (a^2 + b^2 + c^2) by positivity)]
    exact h_lt_sqrt
  · -- Case where a + b + c < 0.
    have h_neg : a + b + c < 0 := by linarith
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (3 * (a ^ 2 + b ^ 2 + c ^ 2)) := Real.sqrt_nonneg _
    nlinarith [Real.sqrt_nonneg (3 * (a ^ 2 + b ^ 2 + c ^ 2)), Real.sq_sqrt (show 0 ≤ (3 * (a^2 + b^2 + c^2) : ℝ) by positivity), h_neg, Real.sqrt_nonneg (3 * (a^2 + b^2 + c^2))]