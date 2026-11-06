import Mathlib

theorem algebra_125790 (a b c : ℝ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
    (h₃ : a + b > c) (h₄ : a + c > b) (h₅ : b + c > a) :
    ¬∃ x : ℝ, b^2 * x^2 + (b^2 + c^2 - a^2) * x + c^2 = 0 := by
  rintro ⟨x, hx⟩
  have h6 : 0 < a + b - c := by linarith
  have h7 : 0 < a + c - b := by linarith
  have h8 : 0 < b + c - a := by linarith
  nlinarith [sq_nonneg (b^2 * x + (b^2 + c^2 - a^2) / 2), sq_nonneg (c), sq_nonneg (a - b - c), 
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂,
          mul_pos h₀ (show 0 < a + b - c by linarith), 
          mul_pos h₀ (show 0 < a + c - b by linarith), 
          mul_pos h₀ (show 0 < b + c - a by linarith), 
          mul_pos h₁ (show 0 < a + b - c by linarith), 
          mul_pos h₁ (show 0 < a + c - b by linarith), 
          mul_pos h₁ (show 0 < b + c - a by linarith), 
          mul_pos h₂ (show 0 < a + b - c by linarith), 
          mul_pos h₂ (show 0 < a + c - b by linarith), 
          mul_pos h₂ (show 0 < b + c - a by linarith), 
          mul_pos (show 0 < a + b - c by linarith) 
            (show 0 < a + c - b by linarith), 
          mul_pos (show 0 < a + b - c by linarith) 
            (show 0 < b + c - a by linarith), 
          mul_pos (show 0 < a + c - b by linarith) 
            (show 0 < b + c - a by linarith)]