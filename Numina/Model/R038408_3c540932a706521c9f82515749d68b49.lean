import Mathlib

open BigOperators Real Set

theorem algebra_22143 :
  IsLeast {y : ℝ | ∃ x, 0 ≤ -x^2 + 4 * x + 21 ∧ 0 ≤ -x^2 + 3 * x + 10 ∧ y = sqrt (-x^2 + 4 * x + 21) - sqrt (-x^2 + 3 * x + 10)} (sqrt 2) := by
  constructor
  · -- Show sqrt 2 is in the set, via x = 1/3
    use 1 / 3
    constructor
    · -- Show 0 ≤ -(1/3) ^ 2 + 4 * (1/3) + 21
      norm_num
    constructor
    · -- Show 0 ≤ -(1/3) ^ 2 + 3 * (1/3) + 10
      norm_num
    · -- Show sqrt 2 = sqrt (-(1/3) ^ 2 + 4 * (1/3) + 21) - sqrt (-(1/3) ^ 2 + 3 * (1/3) + 10)
      have h1 : sqrt (- (1 / 3: ℝ) ^ 2 + 4 * (1 / 3: ℝ) + 21) = 10 * Real.sqrt 2 / 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h2 : sqrt (- (1 / 3: ℝ) ^ 2 + 3 * (1 / 3: ℝ) + 10) = 7 * Real.sqrt 2 / 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h1, h2]
      linarith
  · -- Show sqrt 2 ≤ y for all y in the set
    intro y hy
    rcases hy with ⟨x, hx1, hx2, hy⟩
    have h1 : 0 ≤ -x ^ 2 + 4 * x + 21 := by linarith
    have h2 : 0 ≤ -x ^ 2 + 3 * x + 10 := by linarith
    have h3 : sqrt 2 ≤ sqrt (-x ^ 2 + 4 * x + 21) - sqrt (-x ^ 2 + 3 * x + 10) := by
      have h4 : sqrt 2 + sqrt (-x ^ 2 + 3 * x + 10) ≤ sqrt (-x ^ 2 + 4 * x + 21) := by
        have h5 : (sqrt 2 + sqrt (-x ^ 2 + 3 * x + 10)) ^ 2 ≤ (sqrt (-x ^ 2 + 4 * x + 21)) ^ 2 := by
          have h6 : (sqrt 2 + sqrt (-x ^ 2 + 3 * x + 10)) ^ 2 = (sqrt 2) ^ 2 + (sqrt (-x ^ 2 + 3 * x + 10)) ^ 2 + 2 * (sqrt 2 * sqrt (-x ^ 2 + 3 * x + 10)) := by ring
          rw [h6]
          have h7 : (sqrt (-x ^ 2 + 4 * x + 21)) ^ 2 = -x^2 + 4 * x + 21 := by
            rw [Real.sq_sqrt]
            nlinarith
          have h8 : (sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
          have h9 : (sqrt (-x ^ 2 + 3 * x + 10)) ^ 2 = (-x^2 + 3 * x + 10 : ℝ) := by
            rw [Real.sq_sqrt]
            nlinarith
          rw [h7, h8, h9] at *
          nlinarith [Real.sqrt_nonneg (-x ^ 2 + 3 * x + 10), Real.sqrt_nonneg 2, sq_nonneg (x - 1 / 3), sq_nonneg (sqrt 2 ^ 2 - 2), sq_nonneg (sqrt (-x ^ 2 + 3 * x + 10) ^ 2 - 98 / 9), sq_nonneg (sqrt 2 * sqrt (-x ^ 2 + 3 * x + 10) - 7 * 2 / 9), sq_nonneg (x - 1 / 3), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ -x ^ 2 + 3 * x + 10 by nlinarith), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (-x^2 + 3 * x + 10)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 1 / 3), sq_nonneg (3 * x - 1)]
        have h4' : sqrt 2 + sqrt (-x ^ 2 + 3 * x + 10) ≥ 0 := by positivity
        have h4'' : sqrt (-x ^ 2 + 4 * x + 21) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (-x ^ 2 + 3 * x + 10), Real.sqrt_nonneg (-x ^ 2 + 4 * x + 21)]
      linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (-x ^ 2 + 3 * x + 10), Real.sqrt_nonneg (-x ^ 2 + 4 * x + 21)]
    linarith