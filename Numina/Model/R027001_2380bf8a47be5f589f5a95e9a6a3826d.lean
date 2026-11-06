import Mathlib

open Real Set

theorem inequalities_220196 (x : ℝ) :
    0 ≤ 1 + x ∧ 0 ≤ 3 - x ∧ sqrt (1 + x) + 2 / 5 < sqrt (3 - x) ↔
    -1 ≤ x ∧ x < 11 / 25 := by
  constructor
  · -- Forward direction: from the existence of the inequality, conclude the range of x
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : -1 ≤ x := by linarith
    have h5 : x < 11 / 25 := by
      by_contra h
      push_neg at h
      have h6 : sqrt (1 + x) ≥ 0 := by apply Real.sqrt_nonneg
      have h7 : sqrt (3 - x) ≥ 0 := by apply Real.sqrt_nonneg
      have h8 : 1 + x ≥ 0 := by linarith
      have h9 : 3 - x ≥ 0 := by linarith
      have h11 : sqrt (1 + x) + 2 / 5 ≥ sqrt (3 - x) := by
        have h12 : (sqrt (1 + x) + 2 / 5) ^ 2 ≥ (sqrt (3 - x)) ^ 2 := by
          nlinarith [Real.sq_sqrt h8, Real.sq_sqrt h9,
            h, Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (3 - x),
            sq_nonneg (sqrt (1 + x) - 6 / 5), sq_nonneg (sqrt (3 - x) - 8 / 5),
            Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (3 - x)]
        nlinarith [Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (3 - x),
          Real.sq_sqrt h8, Real.sq_sqrt h9]
      linarith
    constructor
    · -- Forward direction
      linarith
    · -- Forward direction
      linarith
  · -- Backward direction: from the range of x, prove the inequality
    rintro ⟨h₅, h₆⟩
    constructor
    · -- Show 0 <= 1 + x
      linarith
    constructor
    · -- Show 0 <= 3 - x
      linarith
    · -- Show sqrt(1 + x) + 2/5 < sqrt(3 - x)
      have h4 : 1 + x ≥ 0 := by linarith
      have h5 : 3 - x ≥ 0 := by linarith
      have h4' : sqrt (1 + x) ≥ 0 := by apply Real.sqrt_nonneg
      have h5' : sqrt (3 - x) ≥ 0 := by apply Real.sqrt_nonneg
      have h6 : sqrt (1 + x) + 2 / 5 < sqrt (3 - x) := by
        have h12 : (sqrt (1 + x) + 2 / 5) ^ 2 < (sqrt (3 - x)) ^ 2 := by
          nlinarith [Real.sq_sqrt h4, Real.sq_sqrt h5, sq_nonneg (sqrt (1 + x) - 6 / 5), sq_nonneg (sqrt (3 - x) - 8 / 5),
            Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (3 - x),
            mul_nonneg (Real.sqrt_nonneg (1 + x)) (Real.sqrt_nonneg (3 - x)),
            h₅, h₆]
        nlinarith [Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (3 - x),
          Real.sq_sqrt h4, Real.sq_sqrt h5]
      linarith