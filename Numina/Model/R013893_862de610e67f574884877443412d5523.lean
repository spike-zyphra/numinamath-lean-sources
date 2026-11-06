import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_271105 (f : ℝ → ℝ) (hf : f = λ x => (x - 1)^5 / (10 * x - 6)^9)
  (x : ℝ) (hx : 1 < x) :
  f x ≤ 1 / (2^5 * 9^9) ∧
  ∃ x : ℝ, 1 < x ∧ f x = 1 / (2^5 * 9^9) := by

  have h1 : f x ≤ 1 / (2^5 * 9^9) := by
    have h2 : f x = (x - 1)^5 / (10 * x - 6)^9 := by
      rw [hf]

    rw [h2]
    have h3 : 0 < 10 * x - 6 := by
      nlinarith
    have h4 : (x - 1) ^ 5 / (10 * x - 6) ^ 9 ≤ 1 / (2^5 * 9^9) := by
      have h3 : (10 * x - 6 : ℝ) > 0 := by
        nlinarith
      have h5 : (x - 1 : ℝ) > 0 := by
        nlinarith
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h6 : (x - 1 : ℝ) ^ 5 * (2 ^ 5 * (9 : ℝ) ^ 9) ≤ (10 * x - 6) ^ 9 := by
        nlinarith [sq_nonneg ((x - 1.5 : ℝ) ), sq_nonneg ((x - 1 : ℝ) ^ 2 - (0.5 : ℝ) ^ 2), sq_nonneg ((10 * x - 6 - 9 : ℝ) ), sq_nonneg ((x - 1 : ℝ) * (x - 1.5 : ℝ) ), sq_nonneg ((10 * x - 6 - 15) * (x - 1.5 : ℝ) ), sq_nonneg ((x - 1 : ℝ) - (0.5 : ℝ) ), mul_pos (show (0 : ℝ) < x - 1 by linarith) (show (0 : ℝ) < 10 * x - 6 by nlinarith ), pow_pos (show (0 : ℝ) < x - 1 by linarith ) 4, pow_pos (show (0 : ℝ) < x - 1 by linarith ) 2, pow_pos (show (0 : ℝ) < x - 1 by linarith ) 5, pow_pos (show (0 : ℝ) < 10 * x - 6 by nlinarith ) 2, pow_pos (show (0 : ℝ) < 10 * x - 6 by nlinarith ) 4, pow_pos (show (0 : ℝ) < 10 * x - 6 by nlinarith ) 9, sq_nonneg ((x - 1 : ℝ) - (1 : ℝ) / 2), sq_nonneg ((10 * x - 6) - 9), sq_nonneg ((x - 1.5) ^ 2) ]
      linarith
    linarith

  have h2 : ∃ x : ℝ, 1 < x ∧ f x = 1 / (2^5 * 9^9) := by
    use (3 / 2 : ℝ)
    constructor
    · norm_num
    · rw [hf]
      norm_num

  constructor
  · exact h1
  · exact h2