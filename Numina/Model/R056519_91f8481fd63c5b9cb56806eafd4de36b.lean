import Mathlib

theorem algebra_13425 (x : ℝ) :
    (3 * x - 3 ≥ 0 ∧ 5 * x - 19 ≥ 0 ∧ 2 * x + 8 ≥ 0 ∧
     Real.sqrt (3 * x - 3) + Real.sqrt (5 * x - 19) - Real.sqrt (2 * x + 8) = 0) ↔ x = 4 := by
  constructor
  · -- Assume the equation and square roots are defined, prove x = 4
    intro h
    rcases h with ⟨h1, h2, h3, heq⟩
    have h_eq : Real.sqrt (3 * x - 3) + Real.sqrt (5 * x - 19) = Real.sqrt (2 * x + 8) := by linarith
    have h_eq1 : (Real.sqrt (3 * x - 3) + Real.sqrt (5 * x - 19)) ^ 2 = (Real.sqrt (2 * x + 8)) ^ 2 := by 
        rw [h_eq]
    have h_eq2 : (Real.sqrt (3 * x - 3) + Real.sqrt (5 * x - 19)) ^ 2 = Real.sqrt (3 * x - 3) ^ 2 + Real.sqrt (5 * x - 19) ^ 2 + 2 * (Real.sqrt (3 * x - 3) * Real.sqrt (5 * x - 19)) := by ring
    have h_eq3 : (Real.sqrt (2 * x + 8)) ^ 2 = 2 * x + 8 := by 
      apply Real.sq_sqrt 
      linarith
    have h_eq4 : Real.sqrt (3 * x - 3) ^ 2 = 3 * x - 3 := by 
      apply Real.sq_sqrt 
      linarith
    have h_eq5 : Real.sqrt (5 * x - 19) ^ 2 = 5 * x - 19 := by 
      apply Real.sq_sqrt 
      linarith
    rw [h_eq2, h_eq3, h_eq4, h_eq5] at h_eq1
    have h_eq8 : Real.sqrt (3 * x - 3) * Real.sqrt (5 * x - 19) = Real.sqrt ((3 * x - 3) * (5 * x - 19)) := by 
      rw [← Real.sqrt_mul (by nlinarith)]
      all_goals nlinarith 
    have h_eq9 : Real.sqrt ((3 * x - 3) * (5 * x - 19)) = 15 - 3 * x := by
      nlinarith [Real.sqrt_nonneg ((3 * x - 3) * (5 * x - 19)), Real.sqrt_nonneg (2 * x + 8), Real.sqrt_nonneg (3 * x - 3), Real.sqrt_nonneg (5 * x - 19)]
    have h_eq10 : Real.sqrt ((3 * x - 3) * (5 * x - 19)) ^ 2 = (15 - 3 * x) ^ 2 := by 
      rw [h_eq9]
    have h_eq11 : Real.sqrt ((3 * x - 3) * (5 * x - 19)) ^ 2 = (3 * x - 3) * (5 * x - 19) := by 
      apply Real.sq_sqrt 
      nlinarith
    have h_eq12 : (x - 4) * (x + 7) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h_eq12) with h_eq13 h_eq14
    · -- Case x = 4
      linarith
    · -- Case x = -7, which is not in the domain
      nlinarith 
  · -- Assume x = 4 prove the conditions
    intro h_eq
    rw [h_eq]
    constructor
    · norm_num 
    constructor
    · norm_num 
    constructor
    · norm_num 
    · -- Verify the equation 
      have h_eq9 : Real.sqrt (3 * (4 : ℝ) - 3) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h_eq2 : Real.sqrt (5 * (4 : ℝ) - 19) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      have h_eq3 : Real.sqrt (2 * (4 : ℝ) + 8) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h_eq9, h_eq2, h_eq3]
      all_goals norm_num