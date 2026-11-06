import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_105425 :
  IsLeast {y : ℝ | ∃ x, y = sqrt (x^4 / 16 + x^2 / 2 + 1) + sqrt (x^4 / 16 - 4 * x + 8)} 3 := by
  constructor
  · -- First part: show 3 is in the set
    use 2
    have h5 : sqrt (2^4 / 16 + 2^2 / 2 + 1) + sqrt (2^4 / 16 - 4 * 2 + 8) = 3 := by
      have h1 : (2^4 / 16 + 2^2 / 2 + 1 : ℝ) = 4 := by norm_num
      have h2 : (2^4 / 16 - 4 * 2 + 8 : ℝ) = 1 := by norm_num
      have h3 : sqrt (2^4 / 16 + 2^2 / 2 + 1) = (2 : ℝ) := by
        rw [h1]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h4 : sqrt (2^4 / 16 - 4 * 2 + 8) = (1 : ℝ) := by
        rw [h2]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h3, h4]
      all_goals norm_num
    linarith [h5]
  · -- Second part: show 3 is indeed the least element
    intro y hy
    rcases hy with ⟨x, h_eq⟩
    by_cases h : x < 2
    · -- Case 1: x < 2
      have h3 : sqrt (x ^ 4 / 16 + x ^ 2 / 2 + 1) + sqrt (x ^ 4 / 16 - 4 * x + 8) ≥ 3 := by
        have h11 : sqrt (x^4 / 16 + x^2 / 2 + 1) = (x^2 + 4) / 4 := by
          have h16 : x^4 / 16 + x^2 / 2 + 1 = ((x^2 + 4) / 4)^2 := by
            ring_nf
          rw [h16]
          have h17 : Real.sqrt (((x^2 + 4) / 4)^2) = (x^2 + 4) / 4 := by
            apply Real.sqrt_sq
            positivity
          rw [h17]
        rw [h11]
        have h19 : ((x^2 + 4) / 4 + sqrt (x ^ 4 / 16 - 4 * x + 8) : ℝ) ≥ (3 : ℝ) := by
          have h18 : (sqrt (x ^ 4 / 16 - 4 * x + 8)) ^ 2 = (x ^ 4 / 16 - 4 * x + 8 : ℝ) := by
            apply Real.sq_sqrt
            nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (x - 2), sq_nonneg (x * (x - 2)), sq_nonneg ((x + 2)), sq_nonneg (x - 2)]
          nlinarith [sq_nonneg ((x - 2 : ℝ)), sq_nonneg ((x ^ 2 - 4 : ℝ)), sq_nonneg ((x * (x - 2)) : ℝ), sq_nonneg ((x + 2 : ℝ)), Real.sqrt_nonneg (x ^ 4 / 16 - 4 * x + 8) ]
        linarith
      linarith [h_eq, h3]
    · -- Case 2: x ≥ 2
      have h8 : x ≥ (2 : ℝ) := by linarith
      have h3 : sqrt (x ^ 4 / 16 + x ^ 2 / 2 + 1) + sqrt (x ^ 4 / 16 - 4 * x + 8) ≥ 3 := by
        have h11 : sqrt (x ^ 4 / 16 + x ^ 2 / 2 + 1) = (x ^ 2 + 4) / 4 := by
          have h16 : x ^ 4 / 16 + x ^ 2 / 2 + 1 = ((x ^ 2 + 4) / 4) ^ 2 := by
            ring_nf
          rw [h16]
          have h17 : Real.sqrt (((x ^ 2 + 4) / 4) ^ 2) = (x ^ 2 + 4) / 4 := by
            apply Real.sqrt_sq
            positivity
          rw [h17]
        have h_nonneg : x ^ 4 / 16 - 4 * x + 8 ≥ 0 := by
          nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (x - 2), sq_nonneg (x * (x - 2)), sq_nonneg ((x + 2)), sq_nonneg (x ^ 2), sq_nonneg (x - 2), sq_nonneg (x * (x - 2)), sq_nonneg ((x - 2) * (x - 2)), sq_nonneg ((x ^ 2 - 4) * (x - 2))]
        rw [h11]
        have h19 : ((x ^ 2 + 4) / 4 + sqrt (x ^ 4 / 16 - 4 * x + 8) : ℝ) ≥ (3 : ℝ) := by
          have h20 : (sqrt (x ^ 4 / 16 - 4 * x + 8)) ^ 2 = (x ^ 4 / 16 - 4 * x + 8 : ℝ) := by
            apply Real.sq_sqrt
            all_goals nlinarith
          nlinarith [sq_nonneg ((x - 2 : ℝ)), sq_nonneg ((x ^ 2 - 4 : ℝ)), sq_nonneg ((x * (x - 2)) : ℝ), sq_nonneg ((x + 2 : ℝ)), Real.sqrt_nonneg (x ^ 4 / 16 - 4 * x + 8) ]
        linarith
      linarith [h_eq, h3]