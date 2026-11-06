import Mathlib

theorem algebra_106 :
    IsLeast {x : ℝ | ∃ a b, x = a^4 + a * b + b^4 ∧ a^2 + b^2 = 1} 0 := by
  constructor
  · -- Show 0 is in the set 
    use Real.sqrt 2 / 2, -Real.sqrt 2 / 2
    constructor 
    · -- Show x = a^4 + a * b + b^4
      have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (2 : ℝ) / 4 := by 
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring
          _ = (2 : ℝ) / 4 := by 
            rw [Real.sq_sqrt]
            all_goals norm_num 
      have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 4 = (1 : ℝ) / 4 := by 
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 4 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 2 := by ring 
          _ = ((2 : ℝ) / 4) ^ 2 := by rw [h1]
          _ = (1 : ℝ) / 4 := by norm_num 
      have h3 : (Real.sqrt 2 / 2 : ℝ) * (-Real.sqrt 2 / 2 : ℝ) = (-1 / 2 : ℝ) := by 
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith [h2, h3]
    · -- Show a^2 + b^2 = 1 
      have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (2 : ℝ) / 4 := by 
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring
          _ = (2 : ℝ) / 4 := by 
            rw [Real.sq_sqrt]
            all_goals norm_num 
      nlinarith [h1, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Show 0 is the least element
    intro x hx 
    rcases hx with ⟨a, b, h_eq, h_eq1⟩
    have h1 : a^4 + b^4 = 1 - 2 * (a^2 * b^2) := by 
      have h : a^4 + b^4 = (a^2 + b^2)^2 - 2 * (a^2 * b^2) := by 
        ring 
      rw [h, h_eq1] 
      all_goals norm_num 
    have h4 : a^4 + a * b + b^4 ≥ 0 := by 
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b + 1 / 2), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a^2 + b^2 - 1)]
    have hx' : x = a^4 + a * b + b^4 := by 
      linarith [h_eq] 
    linarith [hx', h4]