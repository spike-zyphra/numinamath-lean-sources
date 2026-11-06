import Mathlib

open Real

theorem algebra_184122 : ⌊sqrt (6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6))))⌋ = 2 := by
  -- Initial lower bound
  have h31 : 2 ≤ sqrt (6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6)))) := by
    have h2 : sqrt (6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6)))) ≥ sqrt (4 : ℝ) := by
      apply Real.sqrt_le_sqrt
      have h3 : 6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6))) ≥ (4 : ℝ) := by
        nlinarith [show sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6))) ≥ 0 by positivity]
      linarith
    have h3 : sqrt (4 : ℝ) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    nlinarith [h3]

  -- Systematic upper bound approach
  have h1 : sqrt 6 < (3 : ℝ) := by
    have h2 : sqrt 6 < sqrt (9 : ℝ) := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    have h3 : sqrt (9 : ℝ) = (3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith [h2, h3]

  -- Establishing further bounds
  have h11 : sqrt (6 + sqrt 6) < (3 : ℝ) := by
    have h3 : sqrt (6 + sqrt 6) ^ 2 = 6 + sqrt 6 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (6 + sqrt 6), h1, Real.sq_sqrt (show (6 + sqrt 6 : ℝ) ≥ 0 by positivity)]
  
  -- Continuing with bounds
  have h21 : sqrt (6 + sqrt (6 + sqrt 6)) < (3 : ℝ) := by
    have h3 : sqrt (6 + sqrt (6 + sqrt 6)) ^ 2 = 6 + sqrt (6 + sqrt 6) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (6 + sqrt (6 + sqrt 6)), h11, Real.sq_sqrt (show (6 + sqrt (6 + sqrt 6) : ℝ) ≥ 0 by positivity)]
  
  -- Continuing with bounds
  have h31 : sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6))) < (3 : ℝ) := by
    have h3 : sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6))) ^ 2 = 6 + sqrt (6 + sqrt (6 + sqrt 6)) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (6 + sqrt (6 + sqrt (6 + sqrt 6))), h21, Real.sq_sqrt (show (6 + sqrt (6 + sqrt (6 + sqrt 6)) : ℝ) ≥ 0 by positivity)]
  
  -- Final bound
  have h41 : sqrt (6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6)))) < (3 : ℝ) := by
    have h3 : sqrt (6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6)))) ^ 2 = 6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6))) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6)))), h31, Real.sq_sqrt (show (6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6))) : ℝ) ≥ 0 by positivity)]
  
  -- Final representation
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try nlinarith [h31, h41, Real.sqrt_nonneg (6 + sqrt (6 + sqrt (6 + sqrt (6 + sqrt 6))))]