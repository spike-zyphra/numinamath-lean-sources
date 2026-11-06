import Mathlib

/-When flipped, a coin has a probability p of landing heads.
 When flipped twice, it is twice as likely to land on the same side both times as it is to land on each side once.
  What is the larger possible value of p ?-/

theorem algebra_608737 {p: ℝ} {Prob_same_side Prob_each_side: ℝ → ℝ} (h1: Prob_same_side = fun p => p ^ 2 + (1 - p) ^ 2)
(h2: Prob_each_side = fun p => p * (1 - p) + (1 - p) * p) (h: Prob_same_side p= 2 * Prob_each_side p):
(p ≤ (3 + √3) / 6) ∧ (Prob_same_side ((3 + √3) / 6)= 2 * Prob_each_side ((3 + √3) / 6)) := by

  have eq1 : Prob_same_side p = p ^ 2 + (1 - p) ^ 2 := by
    rw [h1]

  have eq2 : Prob_each_side p = p * (1 - p) + (1 - p) * p := by
    rw [h2]

  rw [eq1] at h
  rw [eq2] at h

  have eq3 : 6 * p ^ 2 - 6 * p + 1 = 0 := by
    nlinarith

  have eq4 : p ≤ (3 + Real.sqrt 3) / 6 := by
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), Real.sqrt_nonneg 3 ]

  constructor
  · -- Prove that p ≤ (3 + √3) / 6
    linarith [ eq4 ]
  · -- Check that the probability functions satisfy the equality at (3 + √3)/6
    have eq5 : Prob_same_side ((3 + √3) / 6) = ((3 + √3) / 6) ^ 2 + (1 - ((3 + √3) / 6)) ^ 2 := by 
      rw [h1]
    have eq6 : Prob_each_side ((3 + √3) / 6) = ((3 + √3) / 6) * (1 - ((3 + √3) / 6)) + (1 - ((3 + √3) / 6)) * ((3 + √3) / 6) := by 
      rw [h2]
    rw [eq5, eq6]
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), Real.sqrt_nonneg 3 ]