import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_274994 : IsLeast {y | ∃ x : ℝ, y = abs (cos x) + abs (cos (2 * x))} (Real.sqrt 2 / 2) := by
  constructor
  · -- Show that `Real.sqrt 2 / 2` is in the set.
    use Real.pi / 4
    have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h2 : cos (2 * (Real.pi / 4)) = 0 := by
      have h3 : 2 * (Real.pi / 4) = Real.pi / 2 := by
        ring
      rw [h3]
      rw [cos_pi_div_two]
    rw [h1, h2]
    have h4 : abs (Real.sqrt 2 / 2) = Real.sqrt 2 / 2 := by
      rw [abs_of_nonneg]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h4]
    all_goals norm_num
    all_goals norm_num
  · -- Show that `Real.sqrt 2 / 2` is indeed the minimum
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : abs (cos x) + abs (cos (2 * x)) ≥ Real.sqrt 2 / 2 := by
      have h2 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
        rw [cos_two_mul]
      rw [h2] at *
      by_cases hcos0 : cos x ≥ 0
      · -- If cos x ≥ 0
        by_cases h2cos2' : (2 * (cos x) ^ 2 - 1) ≥ 0
        · -- If cos (2*x) ≥ 0
          rw [show abs (cos x) = cos x by apply abs_of_nonneg hcos0]
          rw [show abs (2 * (cos x) ^ 2 - 1) = (2 * (cos x) ^ 2 - 1 : ℝ) by apply abs_of_nonneg h2cos2']
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (cos x - Real.sqrt 2 / 2), sq_nonneg (cos x + Real.sqrt 2 / 2)]
        · -- If cos (2*x) < 0
          rw [show abs (cos x) = cos x by apply abs_of_nonneg hcos0]
          rw [show abs (2 * (cos x) ^ 2 - 1) = - (2 * (cos x) ^ 2 - 1 : ℝ) by apply abs_of_neg (show (2 * (cos x) ^ 2 - 1) < (0 : ℝ) by linarith)]
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (cos x - Real.sqrt 2 / 4), sq_nonneg (cos x - 0), sq_nonneg (cos x - Real.sqrt 2 / 2)]
      · -- If cos x < 0
        by_cases h2cos2' : (2 * (cos x) ^ 2 - 1) ≥ 0
        · -- If cos (2*x) ≥ 0
          rw [show abs (cos x) = - cos x by apply abs_of_neg (by linarith)]
          rw [show abs (2 * (cos x) ^ 2 - 1) = (2 * (cos x) ^ 2 - 1 : ℝ) by apply abs_of_nonneg h2cos2']
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (cos x + Real.sqrt 2 / 2), sq_nonneg (cos x + 0), sq_nonneg (cos x + Real.sqrt 2 / 2)]
        · -- If cos (2*x) < 0
          rw [show abs (cos x) = - cos x by apply abs_of_neg (by linarith)]
          rw [show abs (2 * (cos x) ^ 2 - 1) = - (2 * (cos x) ^ 2 - 1 : ℝ) by apply abs_of_neg (show (2 * (cos x) ^ 2 - 1) < (0 : ℝ) by linarith)]
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (cos x + Real.sqrt 2 / 2), sq_nonneg (cos x + 0), sq_nonneg (cos x + Real.sqrt 2 / 2)]
    linarith [h1, hx]