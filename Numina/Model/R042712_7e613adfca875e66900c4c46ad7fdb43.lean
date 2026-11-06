import Mathlib

theorem algebra_186858 (x : ℝ) (hx : x^2 + 3 * x - 6 ≥ 0) :
    x^2 + 3 * x - 18 + 4 * Real.sqrt (x^2 + 3 * x - 6) = 0 ↔ x = -5 ∨ x = 2 := by 
  constructor
  · -- Assume the equation holds, prove x=-5 or x=2
    intro h_eq
    have h1 : Real.sqrt (x^2 + 3 * x - 6) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h2 : (Real.sqrt (x ^ 2 + 3 * x - 6)) ^ 2 = x ^ 2 + 3 * x - 6 := by 
      rw [Real.sq_sqrt]
      linarith
    have h3 : x ^ 2 + 3 * x - 18 + 4 * Real.sqrt (x ^ 2 + 3 * x - 6) = 
          (x^2 + 3 * x - 6) - 12 + 4 * Real.sqrt (x^2 + 3 * x - 6) := by
        linarith 
    rw [h3] at h_eq 
    have h4 : ((Real.sqrt (x ^ 2 + 3 * x - 6)) : ℝ) ^ 2 + 4 * (Real.sqrt (x ^ 2 + 3 * x - 6) ) - 12 = 0 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 3 * x - 6), Real.sq_sqrt (show x ^ 2 + 3 * x - 6 ≥ 0 by linarith), h_eq, h2]
    have h5 : (Real.sqrt (x ^ 2 + 3 * x - 6) - 2) * (Real.sqrt (x ^ 2 + 3 * x - 6) + 6) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Real.sqrt (x^2 + 3 * x - 6) - 2 = 0.
      have h8 : Real.sqrt (x^2 + 3 * x - 6) = 2 := by linarith
      have h9 : x^2 + 3 * x - 6 = 4 := by
        calc
          x^2 + 3 * x - 6 = (Real.sqrt (x^2 + 3 * x - 6)) ^ 2 := by
            rw [Real.sq_sqrt]
            linarith
          _ = (2: ℝ) ^2 := by 
            rw [h8]
          _ = (4: ℝ) := by 
            norm_num
      -- Now solving x^2 + 3 * x - 10 =0
      have h10 : x^2 + 3 * x - 10 = 0 := by
        linarith 
      have h11 : (x + 5) * (x - 2) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp h11) with h12 h13
      · -- x = -5
        left 
        linarith 
      · -- x = 2
        right 
        linarith 
    · -- Real.sqrt (x ^ 2 + 3 * x - 6) = -6.
      have h12 : Real.sqrt (x^2 + 3 * x - 6) = -6 := by linarith
      nlinarith [Real.sqrt_nonneg (x^2 + 3 * x - 6), Real.sq_sqrt (show x ^ 2 + 3 * x - 6 ≥ 0 by linarith)]
  · -- Assume x=-5 or x=2, prove the equation.
    rintro (h | h)
    · -- x = -5
      rw [h]
      have h0 : (-5: ℝ)^2 + 3 * (-5: ℝ) - 6 = (4: ℝ) := by norm_num
      have h1 : Real.sqrt ((-5: ℝ) ^ 2 + 3 * (-5: ℝ) - 6) = (2: ℝ) := by 
        rw [h0]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [Real.sqrt_nonneg ((-5: ℝ) ^ 2 + 3 * (-5: ℝ) - 6), h1, Real.sq_sqrt (show (-5: ℝ) ^ 2 + 3 * (-5: ℝ) - 6 ≥ 0 by norm_num)]
    · -- x = 2
      rw [h]
      have h0 : (2: ℝ)^2 + 3 * (2: ℝ) - 6 = (4: ℝ) := by norm_num
      have h1 : Real.sqrt ((2: ℝ) ^ 2 + 3 * (2: ℝ) - 6) = (2: ℝ) := by 
        rw [h0]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [Real.sqrt_nonneg ((2: ℝ) ^ 2 + 3 * (2: ℝ) - 6), h1, Real.sq_sqrt (show (2: ℝ) ^ 2 + 3 * (2: ℝ) - 6 ≥ 0 by norm_num)]