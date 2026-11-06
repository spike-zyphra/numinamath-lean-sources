import Mathlib

theorem inequalities_176913 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - c ^ 2) ^ 2 ≥ 2 := by

  have h1 : c = 1 - a - b := by linarith

  rw [h1]

  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (a * (1 - a - b) - b * (1 - a - b)), 
          sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_nonneg ha hb, mul_nonneg ha (show 0 ≤ (1 - a - b) by 
            nlinarith [show 0 ≤ 1 - a - b by nlinarith]
          ), 
          mul_nonneg hb (show 0 ≤ (1 - a - b) by 
            nlinarith [show 0 ≤ 1 - a - b by nlinarith]
          )
        ]