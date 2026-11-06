import Mathlib

theorem algebra_219580 : IsLeast {(x + 1) * (x + 2) * (x + 3) * (x + 4) + 2019 | x : ℝ} 2018 := by
  constructor
  · -- Let's prove 2018 is in the set
    use (-5 + Real.sqrt 5) / 2
    -- Now we need to simplify and verify the value of the expression
    nlinarith [sq_nonneg ( ( (-5 + Real.sqrt 5) / 2 : ℝ) ^ 2 + 5 * ( (-5 + Real.sqrt 5) / 2 ) + 5 ), 
          sq_nonneg ( (Real.sqrt 5 - 5) / 2 : ℝ ), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
  · -- Now prove that 2018 is the smallest
    intro y
    rintro ⟨x, hx⟩
    have h : (x + 1) * (x + 2) * (x + 3) * (x + 4) + 2019 ≥ 2018 := by
      nlinarith [sq_nonneg (x^2 + 5 * x + 5)]
    linarith [sq_nonneg (x^2 + 5 * x + 5)]