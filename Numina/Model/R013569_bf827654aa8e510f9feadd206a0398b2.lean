import Mathlib

theorem algebra_7315 (x : ℝ) :
    (3 * x ^ 2 - 18 * x + 52 ≥ 0 ∧ 2 * x ^ 2 - 12 * x + 162 ≥ 0 ∧ -x ^ 2 + 6 * x + 280 ≥ 0 ∧
     Real.sqrt (3 * x ^ 2 - 18 * x + 52) + Real.sqrt (2 * x ^ 2 - 12 * x + 162) =
     Real.sqrt (-x ^ 2 + 6 * x + 280)) ↔ x = 3 := by
  constructor
  · -- Assume the equation holds, prove x = 3
    rintro ⟨h1, h2, h3, heq⟩
    have h4 : (Real.sqrt (3 * x ^ 2 - 18 * x + 52) + Real.sqrt (2 * x ^ 2 - 12 * x + 162)) ^ 2 = (Real.sqrt (-x ^ 2 + 6 * x + 280)) ^ 2 := by 
      rw [heq]
    have h5 : (Real.sqrt (3 * x ^ 2 - 18 * x + 52) + Real.sqrt (2 * x ^ 2 - 12 * x + 162)) ^ 2 =
        (Real.sqrt (3 * x ^ 2 - 18 * x + 52)) ^ 2 + (Real.sqrt (2 * x ^ 2 - 12 * x + 162)) ^ 2 + 2 * (Real.sqrt (3 * x ^ 2 - 18 * x + 52) * Real.sqrt (2 * x ^ 2 - 12 * x + 162)) := by ring
    have h6 : (Real.sqrt (-x ^ 2 + 6 * x + 280)) ^ 2 = -x ^ 2 + 6 * x + 280 := by
      apply Real.sq_sqrt
      linarith
    rw [h5, h6] at h4
    have h7 : (Real.sqrt (3 * x ^ 2 - 18 * x + 52)) ^ 2 = 3 * x ^ 2 - 18 * x + 52 := by 
      apply Real.sq_sqrt 
      linarith 
    have h8 : (Real.sqrt (2 * x ^ 2 - 12 * x + 162)) ^ 2 = 2 * x ^ 2 - 12 * x + 162 := by
      apply Real.sq_sqrt 
      linarith 
    rw [h7, h8] at h4 
    nlinarith [Real.sqrt_nonneg (3 * x ^ 2 - 18 * x + 52), Real.sqrt_nonneg (2 * x ^ 2 - 12 * x + 162), Real.sqrt_nonneg (-x ^ 2 + 6 * x + 280), 
        mul_nonneg (Real.sqrt_nonneg (3 * x ^ 2 - 18 * x + 52)) (Real.sqrt_nonneg (2 * x ^ 2 - 12 * x + 162)), 
        sq_nonneg (Real.sqrt (3 * x ^ 2 - 18 * x + 52) - Real.sqrt (2 * x ^ 2 - 12 * x + 162)), 
        sq_nonneg (x - 3)]
  · -- Assume x = 3, prove the equation
    intro heq 
    have h1 : x = 3 := by linarith
    rw [h1]
    constructor
    · norm_num 
    constructor
    · norm_num 
    constructor 
    · norm_num
    · -- show the equation holds
      have h7 : Real.sqrt (3 * (3 : ℝ) ^ 2 - 18 * (3 : ℝ) + 52) = 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h8 : Real.sqrt (2 * (3 : ℝ) ^ 2 - 12 * (3 : ℝ) + 162) = 12 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h9 : Real.sqrt (-(3 : ℝ) ^ 2 + 6 * (3 : ℝ) + 280) = 17 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h7, h8, h9]
      all_goals norm_num