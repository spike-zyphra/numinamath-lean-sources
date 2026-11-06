import Mathlib

open Real
open scoped BigOperators

theorem inequalities_51695 {a b c : ℝ} (ha : a > 0) (hb : b > 0)
  (hc : c = sqrt (a^2 + b^2)) :
  a + b ≤ c * sqrt 2 ∧
  (a + b = c * sqrt 2 ↔ a = b) := by
  have h1 : a + b ≤ c * Real.sqrt 2 := by
    rw [hc]
    have h3 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
      linarith [sq_nonneg (a - b)]
    have h4 : (a + b) ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt 2 := by
      have h7 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := h3
      have h8 : (a + b) ^ 2 ≤ (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt 2) ^ 2 := by
        have h9 : (Real.sqrt (a ^ 2 + b^2) * Real.sqrt (2)) ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 * (Real.sqrt (2)) ^ 2 := by ring
        have h10 : (Real.sqrt (a ^ 2 + b^2)) ^ 2 = a^2 + b^2 := by
          exact Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by nlinarith [sq_nonneg a, sq_nonneg b])
        have h11 : (Real.sqrt (2 : ℝ)) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)
        rw [h9, h10, h11]
        all_goals linarith [h7]
      have h12 : a + b ≥ 0 := by
        linarith
      have h13 : Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt 2 ≥ 0 := by positivity
      have h14 : (a + b) ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt 2 := by
        nlinarith [h8, h12, h13, Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg (2 : ℝ)]
      linarith
    linarith
  constructor
  · -- Prove the first part: $a + b \leq c * \sqrt{2}$
    linarith [h1]
  · -- Prove the second part: $a + b = c * \sqrt{2} \iff a = b$
    constructor
    · -- Assume $a + b = c * \sqrt{2}$, prove $a = b$
      intro heq
      rw [hc] at heq
      have h2 : (a + b) ^ 2 = 2 * (a ^ 2 + b ^ 2) := by
        have h15 : (a + b) ^ 2 = (Real.sqrt (a ^ 2 + b^2) * Real.sqrt 2) ^ 2 := by
          nlinarith [heq, Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg (2)]
        have h9 : (Real.sqrt (a ^ 2 + b^2) * Real.sqrt (2)) ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 * (Real.sqrt (2)) ^ 2 := by
          ring
        have h10 : (Real.sqrt (a ^ 2 + b^2)) ^ 2 = a^2 + b^2 := by
          exact Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by nlinarith [sq_nonneg a, sq_nonneg b])
        have h11 : (Real.sqrt (2 : ℝ)) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)
        nlinarith [h15, h9, h10, h11]
      have h3 : (a - b) ^ 2 = 0 := by
        linarith
      have h4 : a - b = 0 := by nlinarith
      linarith
    · -- Assume $a = b$, prove $a + b = c * \sqrt{2}$
      intro heq
      rw [hc]
      have h2 : a^2 + b^2 = 2 * a ^ 2 := by
        have ha : a = b := by linarith
        rw [show b = a by linarith]
        nlinarith
      have h3 : (a + b) ^ 2 = 2 * (a ^ 2 + b ^ 2) := by
        have ha : a = b := by linarith
        rw [show b = a by linarith]
        nlinarith
      have h4 : (a + b) = (Real.sqrt (a ^ 2 + b^2) * Real.sqrt 2) := by
        have h7 : (a + b) ^ 2 = (Real.sqrt (a ^ 2 + b^2) * Real.sqrt 2) ^ 2 := by
          have h9 : (Real.sqrt (a ^ 2 + b^2) * Real.sqrt (2)) ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 * (Real.sqrt (2)) ^ 2 := by ring
          have h10 : (Real.sqrt (a ^ 2 + b^2)) ^ 2 = a^2 + b^2 := Real.sq_sqrt (by positivity)
          have h11 : (Real.sqrt (2 : ℝ)) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by positivity)
          rw [h9, h10, h11]
          all_goals linarith [h3]
        have h5 : a + b ≥ 0 := by positivity
        have h6 : Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt 2 ≥ 0 := by positivity
        nlinarith [h7, h5, h6, Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg (2 : ℝ)]
      linarith