import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_311515 (f : ℝ → ℝ) (hf : f = λ x => x * abs (1 - x)) :
    {x | f x > 1 / 4} = {x | x > (1 + sqrt 2) / 2} := by
  ext x
  simp [hf]
  constructor
  · -- Forward: if x * |1 - x| > 1/4, then x > (1 + sqrt 2)/2
    intro h
    by_cases h1 : x ≤ 1
    · -- Case x ≤ 1
      rw [abs_of_nonneg (show 1 - x ≥ 0 by linarith)] at h
      -- The assumption h leads to a contradiction
      nlinarith [sq_nonneg (x - 1 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Case x > 1
      push_neg at h1
      rw [abs_of_neg (show 1 - x < 0 by linarith)] at h
      -- Now we can prove it using properties about quadratic
      have h2 : (x - (1 + sqrt 2) / 2) * (x - (1 - sqrt 2) / 2) > 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h3 : x - (1 + sqrt 2) / 2 > 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h1, sq_nonneg (x - (1 + sqrt 2) / 2), sq_nonneg (x - (1 - sqrt 2) / 2)]
      linarith
  · -- Backward: if x > (1 + sqrt 2)/2, then x * |1 - x| > 1/4
    intro h
    by_cases h1 : x ≤ 1
    · -- Contradiction, since (1 + sqrt 2)/2 > 1
      have h2 : (1 + sqrt 2) / 2 > 1 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      -- From h and h2, we get x > 1
      have h3 : x > 1 := by linarith [h, h2]
      -- But h1 says x ≤ 1
      linarith [h3, h1]
    · -- Case x > 1
      push_neg at h1
      rw [abs_of_neg (show 1 - x < 0 by linarith)]
      -- Now we can prove it using properties about quadratic
      have h2 : (x - (1 + sqrt 2) / 2) * (x - (1 - sqrt 2) / 2) > 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      -- Then squaring both sides we get what we want
      have h3 : x * (x - 1) > (1 : ℝ) / 4 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h1, sq_nonneg (x - (1 + sqrt 2) / 2), sq_nonneg (x - (1 - sqrt 2) / 2)]
      linarith