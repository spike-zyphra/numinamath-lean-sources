import Mathlib

theorem algebra_281458 (a b : ℝ) (h1 : a^2 ≥ b^2) (h2 : a + b ≥ 0) (h3 : a - b ≥ 0) :
  {x : ℝ | x^4 - 2 * a * x^2 + b^2 = 0} = 
  {x : ℝ | x = Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2) ∨ 
          x = Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2) ∨
          x = -Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2) ∨ 
          x = -Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2)} := by 
  ext x
  simp only [Set.mem_setOf_eq, and_imp]
  constructor
  · -- Assume x^4 - 2 * a * x^2 + b^2 = 0, prove x in RHS
    intro h_eq
    have h_eq1 : x^4 - 2 * a * x^2 + b^2 = 0 := h_eq
    have h_eq2 : (x^2 - (a + Real.sqrt (a^2 - b^2))) * (x^2 - (a - Real.sqrt (a^2 - b^2))) = 0 := by
      nlinarith [Real.sqrt_nonneg (a ^2 - b ^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by linarith [h1] ) ] 
    cases' (mul_eq_zero.mp h_eq2) with h5 h6
    · -- Case where x^2 = a + Real.sqrt (a^2 - b^2)
      have h51 : x^2 = a + Real.sqrt (a^2 - b^2) := by linarith
      have h54 : x^2 - (a + Real.sqrt (a^2 - b^2)) = (x - (Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2))) * (x + (Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2))) := by
        nlinarith [Real.sqrt_nonneg ((a + b) / 2), Real.sqrt_nonneg ((a - b) / 2), 
          Real.sq_sqrt (show 0 ≤ (a + b) / 2 by nlinarith ), 
          Real.sq_sqrt (show 0 ≤ (a - b) / 2 by nlinarith ), 
          mul_nonneg (Real.sqrt_nonneg ((a + b) / 2)) (Real.sqrt_nonneg ((a - b) / 2)), 
          Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show 0 ≤ a ^2 - b ^2 by nlinarith )
          ]
      have h53 : (x - (Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2))) * (x + (Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2))) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h53) with h55 h56
      · -- Case where x - something = 0
        left
        have h62 : x = Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2) := by 
          linarith 
        linarith
      · -- Case where x + something = 0
        have h57 : x = - (Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2)) := by linarith
        have h58 : x = -Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2) := by
          nlinarith [Real.sqrt_nonneg ((a + b) / 2), Real.sqrt_nonneg ((a - b) / 2), Real.sq_sqrt (show 0 ≤ (a + b) / 2 by nlinarith ), Real.sq_sqrt (show 0 ≤ (a - b) / 2 by nlinarith ) ]
        simp [h58]
    · -- Case where x^2 = a - Real.sqrt (a^2 - b^2)
      have h61 : x^2 = a - Real.sqrt (a^2 - b^2) := by linarith
      have h64 : x^2 - (a - Real.sqrt (a^2 - b^2)) = (x - (Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2))) * (x + (Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2))) := by
        nlinarith [Real.sqrt_nonneg ((a + b) / 2), Real.sqrt_nonneg ((a - b) / 2), 
          Real.sq_sqrt (show 0 ≤ (a + b) / 2 by nlinarith ), 
          Real.sq_sqrt (show 0 ≤ (a - b) / 2 by nlinarith ), 
          mul_nonneg (Real.sqrt_nonneg ((a + b) / 2)) (Real.sqrt_nonneg ((a - b) / 2)), 
          Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show 0 ≤ a ^2 - b ^2 by nlinarith )
          ]
      have h63 : (x - (Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2))) * (x + (Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2))) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h63) with h64 h65
      · -- Case where x - (sqrt (a + b / 2) - sqrt (a - b / 2)) = 0
        right
        left
        have h651 : x = Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2) := by
          linarith
        linarith
      · -- Case where x + (sqrt (a + b / 2) - sqrt (a - b / 2)) = 0
        right
        right
        left
        have h651 : x = - (Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2)) := by
          linarith
        have h66 : x = -Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2) := by
          nlinarith [Real.sqrt_nonneg ((a + b) / 2), Real.sqrt_nonneg ((a - b) / 2), Real.sq_sqrt (show 0 ≤ (a + b) / 2 by nlinarith ), Real.sq_sqrt (show 0 ≤ (a - b) / 2 by nlinarith ) ]
        linarith
  · -- Assume x in RHS, prove x^4 - 2*a*x^2 + b^2 = 0
    rintro (h_eq | h_eq | h_eq | h_eq)
    · -- First case: x = Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2)
      have h_eq1 : x^2 = a + Real.sqrt (a^2 - b^2) := by
        rw [h_eq]
        nlinarith [Real.sqrt_nonneg ((a + b) / 2), Real.sqrt_nonneg ((a - b) / 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a + b) / 2 by nlinarith ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a - b) / 2 by nlinarith ), 
          mul_nonneg (Real.sqrt_nonneg ((a + b) / 2)) (Real.sqrt_nonneg ((a - b) / 2)), 
          Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by nlinarith ) 
          ]
      nlinarith [Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by nlinarith ) ]
    · -- Second case: x = Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2)
      have h_eq1 : x^2 = a - Real.sqrt (a^2 - b^2) := by
        rw [h_eq]
        nlinarith [Real.sqrt_nonneg ((a + b) / 2), Real.sqrt_nonneg ((a - b) / 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a + b) / 2 by nlinarith ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a - b) / 2 by nlinarith ), 
          mul_nonneg (Real.sqrt_nonneg ((a + b) / 2)) (Real.sqrt_nonneg ((a - b) / 2)), 
          Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by nlinarith ) 
          ]
      nlinarith [Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by nlinarith ) ]
    · -- Third case: x = -Real.sqrt ((a + b) / 2) + Real.sqrt ((a - b) / 2)
      have h_eq1 : x^2 = a - Real.sqrt (a^2 - b^2) := by
        rw [h_eq]
        nlinarith [Real.sqrt_nonneg ((a + b) / 2), Real.sqrt_nonneg ((a - b) / 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a + b) / 2 by nlinarith ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a - b) / 2 by nlinarith ), 
          mul_nonneg (Real.sqrt_nonneg ((a + b) / 2)) (Real.sqrt_nonneg ((a - b) / 2)), 
          Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by nlinarith ) 
          ]
      nlinarith [Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by nlinarith ) ]
    · -- Fourth case: x = -Real.sqrt ((a + b) / 2) - Real.sqrt ((a - b) / 2)
      have h_eq1 : x^2 = a + Real.sqrt (a^2 - b^2) := by
        rw [h_eq]
        nlinarith [Real.sqrt_nonneg ((a + b) / 2), Real.sqrt_nonneg ((a - b) / 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a + b) / 2 by nlinarith ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a - b) / 2 by nlinarith ), 
          mul_nonneg (Real.sqrt_nonneg ((a + b) / 2)) (Real.sqrt_nonneg ((a - b) / 2)), 
          Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by nlinarith ) 
          ]
      nlinarith [Real.sqrt_nonneg (a^2 - b^2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^2 - b ^2 by nlinarith ) ]