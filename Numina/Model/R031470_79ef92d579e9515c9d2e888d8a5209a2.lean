import Mathlib

theorem inequalities_8641 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hord : a ≥ b ∧ b ≥ c) :
    a / b + b / c + c / a ≤ b / a + c / b + a / c := by
  have h1 : 0 < a * b * c := by
    positivity

  have h2 : a / b + b / c + c / a - (b / a + c / b + a / c) ≤ 0 := by
    have h2' : a / b + b / c + c / a - (b / a + c / b + a / c) =
        (a^2 * c + a * b^2 + b * c^2 - b^2 * c - a * c^2 - a^2 * b) / (a * b * c) := by 
      field_simp
      ring 
    rw [h2']
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is non-positive 
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (a - c)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (a - c)), 
          mul_nonneg (show 0 ≤ a - b by linarith [hord.left, hord.right]) 
            (show 0 ≤ b - c by linarith [hord.right]), 
          mul_nonneg (show 0 ≤ a - b by linarith [hord.left, hord.right]) 
            (show 0 ≤ c by linarith [hc]), 
          mul_nonneg (show 0 ≤ b - c by linarith [hord.right]) 
            (show 0 ≤ c by linarith [hc]), 
          mul_nonneg (show 0 ≤ a by linarith [ha]) 
            (show 0 ≤ b - c by linarith [hord.right]), 
          mul_nonneg (show 0 ≤ a by linarith [ha]) 
            (show 0 ≤ a - b by linarith [hord.left, hord.right])
        ]
    · -- Show the denominator is non-negative 
      positivity
  linarith [h2]