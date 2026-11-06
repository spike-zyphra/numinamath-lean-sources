import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_306513 :
  IsGreatest {x | ∃ a b : ℝ, x = sqrt (cos (4*a) + 7) + sqrt (cos (4*b) + 7) +
    sqrt (cos (4*a) + cos (4*b) - 8*(sin a)^2 * (sin b)^2 + 6)} (6*sqrt 2) := by
  constructor
  · -- Show 6*sqrt 2 is in the set
    use 0, 0
    have h1 : sqrt (cos (4 * (0 : ℝ)) + 7) = 2 * sqrt 2 := by
      have h2 : cos (4 * (0 : ℝ)) = 1 := by
        simp
      rw [h2]
      have h3 : sqrt (1 + 7 : ℝ) = 2 * sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      exact h3
    have h3 : sqrt (cos (4 * (0 : ℝ)) + 7) = 2 * sqrt 2 := by -- same as h1
      have h4 : cos (4 * (0 : ℝ)) = 1 := by
        simp
      rw [h4]
      have h5 : sqrt (1 + 7 : ℝ) = 2 * sqrt 2 := by -- same as h1
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      exact h5
    have h4 : sqrt (cos (4 * (0 : ℝ)) + cos (4 * (0 : ℝ)) - 8 * (sin (0 : ℝ)) ^ 2 * (sin (0 : ℝ)) ^ 2 + 6) = 2 * sqrt 2 := by
      have h5 : cos (4 * (0 : ℝ)) = 1 := by
        simp
      have h6 : sin (0 : ℝ) = 0 := by
        simp
      rw [h5, h6]
      have h7 : sqrt (1 + 1 - 8 * (0) ^ 2 * (0) ^ 2 + (6 : ℝ)) = 2 * sqrt 2 := by
        have h8 : (1 + 1 - 8 * (0 : ℝ) ^ 2 * (0 : ℝ) ^ 2 + (6 : ℝ) ) = (8 : ℝ) := by
          norm_num
        rw [h8]
        have h9 : sqrt (8 : ℝ) = 2 * sqrt 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        exact h9
      exact h7
    linarith [h1, h3, h4]
  · -- Show no greater value is in the set
    intro x hx
    rcases hx with ⟨a, b, hx⟩
    have h1 : cos (4 * a) ≤ 1 := by 
      apply cos_le_one
    have h2 : cos (4 * b) ≤ 1 := by 
      apply cos_le_one
    have h3 : cos (4 * a) + 7 ≤ 8 := by 
      linarith [show cos (4 * a) ≤ 1 by apply cos_le_one]
    have h4 : cos (4 * b) + 7 ≤ 8 := by 
      linarith [show cos (4 * b) ≤ 1 by apply cos_le_one]
    have h8 : cos (4 * a) + cos (4 * b) - 8 * (sin a) ^ 2 * (sin b) ^ 2 ≤ 2 := by
      have h9 : sin a ^ 2 ≤ 1 := by 
        apply sin_sq_le_one
      have h10 : sin b ^ 2 ≤ 1 := by 
        apply sin_sq_le_one
      have h11 : cos (4 * a) ≤ 1 := by 
        apply cos_le_one
      have h12 : cos (4 * b) ≤ 1 := by 
        apply cos_le_one
      nlinarith [ sq_nonneg (sin a - 0), sq_nonneg (sin b - 0), 
          sq_nonneg (cos (2 * a) - 1), sq_nonneg (cos (2 * b) - 1), 
          cos_sq_add_sin_sq a, cos_sq_add_sin_sq b, 
          sq_nonneg (cos (4 * a) - 1), sq_nonneg (cos (4 * b) - 1), 
          sq_nonneg (sin a - 0), sq_nonneg (sin b - 0)
        ]
    have h5 : cos (4 * a) + cos (4 * b) - 8 * (sin a) ^ 2 * (sin b) ^ 2 + 6 ≤ 8 := by 
      linarith [h8]
    have h6 : sqrt (cos (4 * a) + 7) ≤ 2 * sqrt 2 := by
      have h7 : cos (4 * a) + 7 ≤ 8 := by 
        linarith [show cos (4 * a) ≤ 1 by apply cos_le_one]
      have h8 : sqrt (cos (4 * a) + 7) ≤ sqrt (8 : ℝ) := Real.sqrt_le_sqrt (by linarith [h7])
      have h9 : sqrt (8 : ℝ) = 2 * sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h8, h9]
    have h7 : sqrt (cos (4 * b) + 7) ≤ 2 * sqrt 2 := by 
      have h8 : cos (4 * b) + 7 ≤ 8 := by 
        linarith [show cos (4 * b) ≤ 1 by apply cos_le_one]
      have h9 : sqrt (cos (4 * b) + 7) ≤ sqrt (8 : ℝ) := Real.sqrt_le_sqrt (by linarith [h8])
      have h10 : sqrt (8 : ℝ) = 2 * sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h9, h10]
    have h8 : sqrt (cos (4 * a) + cos (4 * b) - 8 * (sin a) ^ 2 * (sin b) ^ 2 + 6) ≤ 2 * sqrt 2 := by 
      have h9 : cos (4 * a) + cos (4 * b) - 8 * (sin a) ^ 2 * (sin b) ^ 2 + 6 ≤ (8 : ℝ) := by 
        linarith [h8]
      have h10 : sqrt (cos (4 * a) + cos (4 * b) - 8 * (sin a) ^ 2 * (sin b) ^ 2 + 6) ≤ sqrt (8 : ℝ) := Real.sqrt_le_sqrt (by linarith [h9])
      have h11 : sqrt (8 : ℝ) = 2 * sqrt 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h10, h11]
    nlinarith [hx, h6, h7, h8]