import Mathlib

theorem algebra_298009 (x : ℝ) :
    x^2 - 2 * x * Real.sin (Real.pi * x / 2) + 1 = 0 ↔ x = 1 ∨ x = -1 := by
  constructor 
  · -- First direction: the equation holds implies the solutions
    intro h 
    by_cases h3 : x > 0 
    · -- Assume x > 0
      have hx1 : x = 1 := by
        have h10 : Real.sin (Real.pi * x / 2) ^2 ≤1 := Real.sin_sq_le_one (Real.pi * x / 2)
        have h13 : x ^ 2 +1 = 2 * x * Real.sin (Real.pi * x / 2) := by nlinarith 
        have h60 : (x - 1) ^ 2 =0 := by
          have h70 : Real.sin (Real.pi * x / 2) ≤1 := by
            apply Real.sin_le_one 
          have h80 : Real.sin (Real.pi * x / 2) ≥-1 := by 
            apply Real.neg_one_le_sin 
          nlinarith [Real.sin_sq_le_one (Real.pi * x / 2), sq_nonneg (x -1), sq_nonneg (Real.sin (Real.pi * x / 2) -1), Real.sin_sq_le_one (Real.pi * x / 2)]
        have h7 : x -1 =0 := by 
          nlinarith
        linarith 
      left
      exact hx1 
    by_cases h3 : x < 0 
    · -- Assume x < 0 
      have hx1 : x = -1 := by 
        have h10 : Real.sin (Real.pi * x / 2) ^2 ≤1 := Real.sin_sq_le_one (Real.pi * x / 2)
        have h13 : x ^ 2 +1 = 2 * x * Real.sin (Real.pi * x / 2) := by nlinarith 
        have h60 : (x + 1) ^ 2 =0 := by 
          have h70 : Real.sin (Real.pi * x / 2) ≤1 := by
            apply Real.sin_le_one 
          have h80 : Real.sin (Real.pi * x / 2) ≥-1 := by
            apply Real.neg_one_le_sin 
          nlinarith [Real.sin_sq_le_one (Real.pi * x / 2), sq_nonneg (x +1), sq_nonneg (Real.sin (Real.pi * x / 2) +1), Real.sin_sq_le_one (Real.pi * x / 2)]
        have h7 : x +1 =0 := by
          nlinarith 
        linarith 
      right
      exact hx1 
    · -- Case x = 0 
      have h4 : x = 0 := by 
        linarith
      rw [h4] at h 
      nlinarith [Real.sin_sq_le_one (Real.pi * (0 : ℝ) / 2)]
  · -- Second direction: prove if the values satisfy then solutions
    rintro (hx | hx)
    · -- When x = 1 
      rw [hx]
      have h1 : Real.sin (Real.pi * (1 : ℝ) / 2) = 1 := by 
        have h2 : Real.sin (Real.pi * (1 : ℝ) / 2) = Real.sin (Real.pi / 2 : ℝ) := by ring_nf
        rw [h2]
        exact Real.sin_pi_div_two
      rw [h1]
      norm_num 
    · -- When x = -1 
      rw [hx]
      have h1 : Real.sin (Real.pi * (-1 : ℝ) / 2) = -1 := by
        have h2 : Real.sin (Real.pi * (-1 : ℝ) / 2) = Real.sin (- (Real.pi / 2 : ℝ) ) := by ring_nf
        rw [h2]
        have h3 : Real.sin (- (Real.pi / 2 : ℝ) ) = - Real.sin (Real.pi / 2 : ℝ) := by
          rw [Real.sin_neg]
        rw [h3]
        have h4 : Real.sin (Real.pi / 2 : ℝ) = 1 := Real.sin_pi_div_two
        rw [h4]
        all_goals norm_num
      rw [h1]
      norm_num