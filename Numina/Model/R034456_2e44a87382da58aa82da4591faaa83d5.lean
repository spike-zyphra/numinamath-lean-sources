import Mathlib

theorem algebra_4031 {a b : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1) (h : a * √(1 - b ^ 2) + b * √(1 - a ^ 2) = 1) :
    a ^ 2 + b ^ 2 = 1 := by 
  have h1 : 0 ≤ 1 - b ^ 2 := by nlinarith
  have h2 : 0 ≤ 1 - a ^ 2 := by nlinarith

  have h3 : (a * √(1 - b ^ 2) + b * √(1 - a ^ 2)) ^ 2 ≤ (a ^ 2 + b ^ 2) * ((1 - b ^ 2) + (1 - a ^ 2)) := by
    nlinarith [sq_nonneg (√(1 - b ^ 2) * b - √(1 - a ^ 2) * a), sq_nonneg (√(1 - b ^ 2) * a - √(1 - a ^ 2) * b), 
          Real.sqrt_nonneg (1 - b ^ 2), Real.sqrt_nonneg (1 - a ^ 2),
          mul_nonneg (Real.sqrt_nonneg (1 - b ^ 2)) (Real.sqrt_nonneg (1 - a ^ 2)),
          Real.sq_sqrt h1, Real.sq_sqrt h2
    ]
  
  have h4 : (a * √(1 - b ^ 2) + b * √(1 - a ^ 2)) ^ 2 = 1 := by
    rw [h]
    all_goals norm_num
  
  have h7 : (a ^ 2 + b ^ 2) = 1 := by
    nlinarith [Real.sqrt_nonneg (1 - b ^ 2), Real.sqrt_nonneg (1 - a ^ 2), 
          sq_nonneg (√(1 - b ^ 2) * a - √(1 - a ^ 2) * b), 
          sq_nonneg (a^2 + b^2 - 1), 
          sq_nonneg (√(1 - b ^ 2)^2 - √(1 - a ^ 2)^2), 
          Real.sq_sqrt h1, Real.sq_sqrt h2, 
          mul_nonneg (Real.sqrt_nonneg (1 - b ^ 2)) (Real.sqrt_nonneg (1 - a ^ 2))
          ]
  
  exact h7