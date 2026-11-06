import Mathlib

theorem number_theory_317 {a b c d : ℝ} (h₀ : 2*a^2+3*c^2=6) (h₁ : 2*b^2+3*d^2=6)
    (h₂ : (a*d-b*c)^2=6) :
    (a^2+b^2)*(c^2+d^2)=6 := by 
  have h3 : 2 * (a^2 + b^2) + 3 * (c^2 + d^2) = 12 := by 
    nlinarith 
  have h7 : (c^2 + d^2 - 2) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (a^2 + b^2 - 3), sq_nonneg (c^2 + d^2 - 2), 
        sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c), 
        sq_nonneg (a * b - c * d), sq_nonneg (a * b + c * d), 
        sq_nonneg (a * c + b * d - 0), sq_nonneg (a * d - b * c)
      ]
  have h8 : c^2 + d^2 = 2 := by 
    nlinarith [h7] 
  have h9 : a^2 + b^2 = 3 := by 
    nlinarith [h8, h3] 
  calc
    (a^2 + b^2) * (c^2 + d^2) = 3 * 2 := by 
      rw [show a^2 + b^2 = 3 by linarith [h9], show c^2 + d^2 = 2 by linarith [h8]]
    _ = (6 : ℝ) := by
      norm_num