import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_180749 :
  IsLeast {x | ∃ t : ℝ, x = abs (cos t) + abs (cos (2 * t))} (Real.sqrt 2 / 2) := by
  constructor
  · -- Show that Real.sqrt 2 / 2 is in the set, using t = Real.pi / 4
    use Real.pi / 4
    have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    have h2 : cos (2 * (Real.pi / 4)) = 0 := by
      have h1 : 2 * (Real.pi / 4) = Real.pi / 2 := by
        ring_nf
      rw [h1]
      rw [cos_pi_div_two]
    
    rw [h1, h2]
    have h3 : abs (Real.sqrt 2 / 2) = Real.sqrt 2 / 2 := by
      apply abs_of_nonneg
      have h4 : Real.sqrt 2 / 2 ≥ 0 := by
        have h5 : Real.sqrt 2 ≥ 0 := by
          apply Real.sqrt_nonneg
        have h6 : Real.sqrt 2 / 2 ≥ 0 := by
          linarith [h5]
        linarith
      linarith
    rw [h3]
    all_goals norm_num
  · -- Show that Real.sqrt 2 / 2 is the least element in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    have ht_eq : x = abs (cos t) + abs (cos (2 * t)) := by
      linarith [ht]
    have h1 : cos (2 * t) = 2 * (cos t) ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [ht_eq]
    rw [h1]
    by_cases h2 : cos t ≥ 0
    · -- cos t ≥ 0
      by_cases h3 : 2 * (cos t) ^ 2 - 1 ≥ 0
      · -- cos t ≥ 0 and 2 * (cos t) ^ 2 - 1 ≥ 0
        rw [abs_of_nonneg h2, abs_of_nonneg h3]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (cos t - Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), sq_nonneg (cos t - 1), sq_nonneg (cos t - (-1)), Real.sqrt_nonneg 2]
      · -- cos t ≥ 0 and 2 * (cos t) ^ 2 - 1 < 0
        rw [abs_of_nonneg h2, abs_of_neg (lt_of_not_ge h3)]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (cos t - Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), sq_nonneg (cos t - 1), sq_nonneg (cos t - (-1)), Real.sqrt_nonneg 2]
    · -- cos t < 0
      by_cases h4 : 2 * (cos t) ^ 2 - 1 ≥ 0
      · -- cos t < 0 and 2 * (cos t) ^ 2 - 1 ≥ 0
        rw [abs_of_neg (lt_of_not_ge h2), abs_of_nonneg h4]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (cos t + Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), sq_nonneg (cos t - 1), sq_nonneg (cos t - (-1)), Real.sqrt_nonneg 2]
      · -- cos t < 0 and 2 * (cos t) ^ 2 - 1 < 0
        rw [abs_of_neg (lt_of_not_ge h2), abs_of_neg (lt_of_not_ge h4)]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (cos t + Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), sq_nonneg (cos t - 1), sq_nonneg (cos t - (-1)), Real.sqrt_nonneg 2]