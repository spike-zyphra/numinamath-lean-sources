import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_240363 (f : ℝ → ℝ)
  (hf : f = λ x => sqrt (4 * x ^ 2 - 12 * x + 8) + sqrt (4 + 3 * x - x ^ 2)) :
  IsLeast {y | ∃ x, y = f x} (sqrt 6) := by
  constructor
  · -- First, prove that sqrt(6) is in the image of f
    use 2
    rw [hf]
    simp
    have h1 : sqrt (4 * (2:ℝ) ^ 2 - 12 * (2:ℝ) + 8) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    have h2 : sqrt (4 + 3 * (2:ℝ) - (2:ℝ) ^ 2) = sqrt 6 := by
      norm_num
    linarith [h1, h2]
  · -- Now, prove no value smaller than sqrt(6) is in the image of f
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h7 : sqrt (4 * x ^ 2 - 12 * x + 8) ≥ 0 := by positivity
    have h8 : sqrt (4 + 3 * x - x ^ 2) ≥ 0 := by positivity
    by_contra h
    push_neg at h
    have h9 : sqrt (4 * x ^ 2 - 12 * x + 8) + sqrt (4 + 3 * x - x ^ 2) < sqrt 6 := by linarith [hx, h7, h8]
    have h10 : sqrt (4 * x ^ 2 - 12 * x + 8) ≥ 0 := by positivity
    have h11 : sqrt (4 + 3 * x - x ^ 2) ≥ 0 := by positivity
    have h12 : (sqrt (4 * x ^ 2 - 12 * x + 8) + sqrt (4 + 3 * x - x ^ 2)) ^ 2 < (sqrt 6) ^ 2 := by nlinarith [h9, Real.sqrt_nonneg (4 * x ^ 2 - 12 * x + 8), Real.sqrt_nonneg (4 + 3 * x - x ^ 2), Real.sqrt_nonneg 6]
    have h13 : (sqrt (4 * x ^ 2 - 12 * x + 8) + sqrt (4 + 3 * x - x ^ 2)) ^ 2 = (sqrt (4 * x ^ 2 - 12 * x + 8)) ^ 2 + (sqrt (4 + 3 * x - x ^ 2)) ^ 2 + 2 * (sqrt (4 * x ^ 2 - 12 * x + 8) * sqrt (4 + 3 * x - x ^ 2)) := by ring
    have h14 : (sqrt 6) ^ 2 = (6 : ℝ) := by
      rw [Real.sq_sqrt]
      all_goals linarith
    have h15 : (sqrt (4 * x ^ 2 - 12 * x + 8)) ^ 2 = (4 * x ^ 2 - 12 * x + 8 : ℝ) := by
      have h15 : 0 ≤ (4 * x ^ 2 - 12 * x + 8 : ℝ) := by
        by_contra h
        push_neg at h
        have h5 : sqrt (4 * x ^ 2 - 12 * x + 8) = 0 := by
          rw [Real.sqrt_eq_zero']
          linarith
        have h6 : sqrt (4 + 3 * x - x ^ 2) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (4 * x ^ 2 - 12 * x + 8), Real.sqrt_nonneg (4 + 3 * x - x ^ 2), hx, Real.sq_sqrt (show (0 : ℝ) ≤ 4 + 3 * x - x ^ 2 by nlinarith)]
      rw [Real.sq_sqrt h15]
    have h16 : (sqrt (4 + 3 * x - x ^ 2)) ^ 2 = (4 + 3 * x - x ^ 2 : ℝ) := by
      have h17 : 0 ≤ (4 + 3 * x - x ^ 2 : ℝ) := by
        by_contra h
        push_neg at h
        have h20 : sqrt (4 + 3 * x - x ^ 2) = 0 := by
          rw [Real.sqrt_eq_zero']
          linarith
        have h18 : sqrt (4 * x ^ 2 - 12 * x + 8) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (4 * x ^ 2 - 12 * x + 8), Real.sqrt_nonneg (4 + 3 * x - x ^ 2), hx, Real.sq_sqrt (show (0 : ℝ) ≤ 4 * x ^ 2 - 12 * x + 8 by nlinarith)]
      rw [Real.sq_sqrt h17]
    nlinarith [h12, h13, h14, h15, h16, Real.sqrt_nonneg (4 * x ^ 2 - 12 * x + 8), Real.sqrt_nonneg (4 + 3 * x - x ^ 2), Real.sqrt_nonneg 6]