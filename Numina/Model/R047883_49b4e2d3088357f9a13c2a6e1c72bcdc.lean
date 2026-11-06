import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_307846 (x : ℝ) :
  sqrt (x^2 - 2 * x + 5) - sqrt (x^2 - 6 * x + 13) ∈ Ioo (-2) 2 := by
  have h7 : sqrt (x ^ 2 - 2 * x + 5) + 2 > sqrt (x ^ 2 - 6 * x + 13) := by
    have h8 : sqrt (x^2 - 2 * x + 5) ^ 2 = x^2 - 2 * x + 5 := by
      rw [Real.sq_sqrt]
      nlinarith [sq_nonneg (x - 1)]
    have h9 : sqrt (x^2 - 6 * x + 13) ^ 2 = x^2 - 6 * x + 13 := by
      rw [Real.sq_sqrt]
      nlinarith [sq_nonneg (x - 3)]
    have h6 : sqrt (x^2 - 2 * x + 5) > -x + 1 := by
      have h2 : x ^ 2 - 2 * x + 5 ≥ 0 := by
        nlinarith [sq_nonneg (x - 1)]
      have h4 : sqrt (x ^ 2 - 2 * x + 5) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 2 * x + 5)
      by_cases h : -x + 1 < 0
      · -- case where -x + 1 < 0
        nlinarith [Real.sqrt_nonneg (x ^ 2 - 2 * x + 5), h]
      · -- case where -x + 1 ≥ 0
        have h8 : -x + 1 ≥ 0 := by linarith
        have h9 : (sqrt (x ^ 2 - 2 * x + 5)) ^ 2 > (-x + 1) ^ 2 := by
          have h10 : (sqrt (x ^ 2 - 2 * x + 5)) ^ 2 = x^2 - 2 * x + 5 := by
            rw [Real.sq_sqrt]
            nlinarith [sq_nonneg (x - 1)]
          nlinarith [h10, sq_nonneg (x - 1)]
        have h10 : sqrt (x ^ 2 - 2 * x + 5) > -x + 1 := by
          nlinarith [Real.sqrt_nonneg (x ^ 2 - 2 * x + 5), h8, h9]
        linarith
    have h11 : (sqrt (x^2 - 2 * x + 5) + 2) ^ 2 > (sqrt (x^2 - 6 * x + 13)) ^ 2 := by
      nlinarith [h6, Real.sqrt_nonneg (x^2 - 2 * x + 5), Real.sqrt_nonneg (x^2 - 6 * x + 13), sq_nonneg (sqrt (x ^ 2 - 2 * x + 5) + 2 - sqrt (x ^ 2 - 6 * x + 13)), sq_nonneg (sqrt (x^2 - 2 * x + 5) - (sqrt (x^2 - 6 * x + 13) - 2))]
    nlinarith [Real.sqrt_nonneg (x^2 - 2 * x + 5), Real.sqrt_nonneg (x^2 - 6 * x + 13), h11]
  have h1 : -2 < sqrt (x^2 - 2 * x + 5) - sqrt (x^2 - 6 * x + 13) := by
    have h7' : sqrt (x^2 - 2 * x + 5) + 2 > sqrt (x^2 - 6 * x + 13) := h7
    linarith [h7']
  have h8 : sqrt (x ^ 2 - 2 * x + 5) - sqrt (x ^ 2 - 6 * x + 13) < 2 := by
    have h2 : x ^ 2 - 2 * x + 5 ≥ 0 := by
      nlinarith [sq_nonneg (x - 1)]
    have h3 : x ^ 2 - 6 * x + 13 ≥ 0 := by
      nlinarith [sq_nonneg (x - 3)]
    have h4 : sqrt (x ^ 2 - 2 * x + 5) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 2 * x + 5)
    have h5 : sqrt (x ^ 2 - 6 * x + 13) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 6 * x + 13)
    have h10 : sqrt (x ^ 2 - 2 * x + 5) < sqrt (x ^ 2 - 6 * x + 13) + 2 := by
      have h11 : (sqrt (x ^ 2 - 2 * x + 5)) ^ 2 < (sqrt (x ^ 2 - 6 * x + 13) + 2) ^ 2 := by
        have h12 : (sqrt (x ^ 2 - 2 * x + 5)) ^ 2 = x ^ 2 - 2 * x + 5 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h13 : (sqrt (x ^ 2 - 6 * x + 13) + 2) ^ 2 = (sqrt (x ^ 2 - 6 * x + 13)) ^ 2 + 4 * sqrt (x ^ 2 - 6 * x + 13) + 4 := by
          ring
        have h14 : (sqrt (x ^ 2 - 6 * x + 13)) ^ 2 = x ^ 2 - 6 * x + 13 := by
          rw [Real.sq_sqrt]
          nlinarith
        nlinarith [h12, h13, h14, sq_nonneg (x - 3), Real.sqrt_nonneg (x ^ 2 - 6 * x + 13)]
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 2 * x + 5), Real.sqrt_nonneg (x ^ 2 - 6 * x + 13), Real.sqrt_nonneg (x ^ 2 - 6 * x + 13)]
    nlinarith [h10, Real.sqrt_nonneg (x ^ 2 - 2 * x + 5), Real.sqrt_nonneg (x ^ 2 - 6 * x + 13)]
  exact ⟨h1, h8⟩