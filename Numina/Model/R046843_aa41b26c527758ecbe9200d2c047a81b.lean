import Mathlib

theorem inequalities_180139 (a b : ℝ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : a + b = 1) :
    (a + 1 / (2 * b ^ 2)) * (b + 1 / (2 * a ^ 2)) ≥ 25 / 4 := by 
  have h2 : 0 < a * b := by
    nlinarith
  have h3 : b = 1 - a := by 
    linarith 
  have h6 : 0 < 4 * a^2 * b^2 := by 
    positivity 
  have h7 : (a + 1 / (2 * b ^ 2)) * (b + 1 / (2 * a ^ 2)) - 25 / 4 ≥ 0 := by 
    have h8 : (a + 1 / (2 * b ^ 2)) * (b + 1 / (2 * a ^ 2)) - 25 / 4 =
        (4 * a^3 * b^3 + 2 * a * b * (a + b) + 1 - 25 * (a * b) ^ 2) / (4 * a^2 * b^2) := by 
      field_simp [(show b ≠ 0 by linarith), (show a ≠ 0 by linarith)]
      ring_nf 
    rw [h8]
    apply div_nonneg 
    have h81 : 0 ≤ 4 * a^3 * b^3 + 2 * a * b * (a + b) + 1 - 25 * (a * b) ^ 2 := by 
      rw [show a + b = 1 by linarith] 
      have h10 : a * b ≤ 1 / 4 := by 
        nlinarith [sq_nonneg (a - b), h₁]
      have h11 : a * b ≥ 0 := by positivity 
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), 
          sq_nonneg (a * b - 1 / 4), 
          sq_nonneg (a - b), 
          mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith), 
          mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < 1 - a by nlinarith), 
          mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < 1 - b by nlinarith)
          ]
    linarith 
    all_goals 
      positivity 
  linarith