import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_218938 {x : ℝ} (hx : 2 ≤ x) :
    3 * sqrt (x - 2) + 4 * x ≤ sqrt ((9 + x ^ 2) * (x + 14)) ∧
    (3 * sqrt (x - 2) + 4 * x = sqrt ((9 + x ^ 2) * (x + 14)) ↔ x = 6) := by

  have h1 : 0 ≤ x - 2 := by linarith
  have h2 : 0 ≤ sqrt (x - 2) := Real.sqrt_nonneg (x - 2)
  have h3 : 0 ≤ 9 + x ^ 2 := by nlinarith
  have h4 : 0 ≤ x + 14 := by nlinarith
  have h5 : 0 ≤ (9 + x ^ 2) * (x + 14) := mul_nonneg (by nlinarith) (by nlinarith)
  have h6 : 0 ≤ sqrt ((9 + x ^ 2) * (x + 14)) := Real.sqrt_nonneg ((9 + x ^ 2) * (x + 14))
  have h7 : (3 * sqrt (x - 2) + 4 * x) ^ 2 ≤ (9 + x ^ 2) * (x + 14) := by
    have h8 : (sqrt (x - 2)) ^ 2 = x - 2 := Real.sq_sqrt (by linarith)
    have h10 : (x ^ 3 - 2 * x ^ 2 + 144) ≥ 24 * x * (sqrt (x - 2)) := by
      have h11 : (x ^ 3 - 2 * x ^ 2 + 144 - 24 * x * (sqrt (x - 2))) ≥ 0 := by
        have h12 : sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
        have h13 : (x ^ 3 - 2 * x ^ 2 + 144 - 24 * x * (sqrt (x - 2))) =
            (x ^ 3 - 2 * x ^ 2 + 144 - 24 * x * (sqrt (x - 2))) := by rfl
        have h14 : (x ^ 3 - 2 * x ^ 2 + 144) ^ 2 ≥ (24 * x * (sqrt (x - 2))) ^ 2 := by
          nlinarith [sq_nonneg (x ^ 3 - 2 * x ^ 2 + 144 - 24 * x * sqrt (x - 2)), sq_nonneg (sqrt (x - 2) - 2), sq_nonneg (x - 6), sq_nonneg (x ^ 2 - 36), Real.sqrt_nonneg (x - 2), sq_nonneg (x * (x - 6)), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith), mul_nonneg (show (0 : ℝ) ≤ x - 2 by linarith) (show (0 : ℝ) ≤ x by linarith)]
        nlinarith [h14, sq_nonneg (sqrt (x - 2)), Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ x - 2 by linarith), sq_nonneg (x ^ 2 - 36), sq_nonneg (x - 6), sq_nonneg (sqrt (x - 2) - 2)]
      linarith
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith), sq_nonneg (x ^ 2 - 36), sq_nonneg (sqrt (x - 2) - 2), sq_nonneg (x - 6), sq_nonneg (x * (x - 6)), Real.sqrt_nonneg (x - 2)]
  have h8 : 3 * sqrt (x - 2) + 4 * x ≤ sqrt ((9 + x ^ 2) * (x + 14)) := by
    have h9 : (3 * sqrt (x - 2) + 4 * x) ^ 2 ≤ (sqrt ((9 + x ^ 2) * (x + 14)) ) ^ 2 := by
      have h10 : (sqrt ((9 + x ^ 2) * (x + 14)) ) ^ 2 = (9 + x ^ 2) * (x + 14) := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [h10, h7]
    have h10 : 0 ≤ 3 * sqrt (x - 2) + 4 * x := by
      have h11 : sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
      nlinarith [h11]
    have h11 : 0 ≤ sqrt ((9 + x ^ 2) * (x + 14)) := Real.sqrt_nonneg ((9 + x ^ 2) * (x + 14))
    nlinarith [h10, h11, Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg ((9 + x ^ 2) * (x + 14))]
  constructor
  · -- First part: proving the inequality
    exact h8
  · -- Second part: proving the bi-directional
    constructor
    · -- Assuming equality holds, prove x = 6
      intro h_eq
      have h_eq1 : (3 * sqrt (x - 2) + 4 * x) ^ 2 = (sqrt ((9 + x ^ 2) * (x + 14)) ) ^ 2 := by
        nlinarith [h_eq, h6, show 0 ≤ 3 * sqrt (x - 2) + 4 * x by
          have h11 : sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
          nlinarith [h11]
, Real.sqrt_nonneg ((9 + x ^ 2) * (x + 14)), Real.sqrt_nonneg (x - 2)]
      have h_eq2 : (3 * sqrt (x - 2) + 4 * x) ^ 2 = (9 + x ^ 2) * (x + 14) := by
        have h_eq3 : (sqrt ((9 + x ^ 2) * (x + 14)) ) ^ 2 = (9 + x ^ 2) * (x + 14) := by
          rw [Real.sq_sqrt]
          positivity
        linarith [h_eq1, h_eq3]
      -- From the equality condition of Cauchy-Schwarz inequality
      have h_eq4 : x = 6 := by
        have h14 : sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
        have h_eq3 : x * sqrt (x - 2) = 12 := by
          have h8 : (sqrt (x - 2)) ^ 2 = x - 2 := Real.sq_sqrt (by linarith)
          nlinarith [Real.sqrt_nonneg (x - 2), sq_nonneg (x - 6), sq_nonneg (sqrt (x - 2) - 2), h8, sq_nonneg (x * (x - 6))]
        have h8 : (sqrt (x - 2)) ^ 2 = x - 2 := Real.sq_sqrt (by linarith)
        nlinarith [sq_nonneg (sqrt (x - 2) - 2), sq_nonneg (x - 6), Real.sqrt_nonneg (x - 2), sq_nonneg (x * (x - 6))]
      assumption
    · -- Assuming x = 6, prove equality
      intro h_eq
      rw [h_eq]
      have h11 : sqrt (6 - 2 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h15 : sqrt ((9 + (6 : ℝ) ^ 2) * (6 + 14 : ℝ)) = 30 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h11, h15]
      all_goals norm_num