import Mathlib

theorem inequalites_92859 (a b c : ℝ) : 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧ c < 1 → a + b + c + 2*a*b*c > a*b + b*c + c*a + 2* √(a*b*c) := by
  intro h
  rcases h with ⟨ha1, ha2, hb1, hb2, hc1, hc2⟩
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : √(a * b * c) ≥ 0 := by positivity
  have h3 : (√(a * b * c)) ^ 2 = a * b * c := by
    rw [Real.sq_sqrt]
    positivity
  have h4 : a + b + c + 2 * a * b * c - (a * b + b * c + c * a) > 0 := by
    nlinarith [mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1, 
              mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith), 
              mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 - c by linarith), 
              mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - c by linarith), 
              mul_pos (mul_pos ha1 hb1) hc1, 
              mul_pos (mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith)) (show 0 < 1 - c by linarith)]
  nlinarith [sq_nonneg (√(a * b * c) - a * b * c), sq_nonneg (√(a * b * c)), sq_nonneg (√(a * b * c) - a), sq_nonneg (√(a * b * c) - b), sq_nonneg (√(a * b * c) - c), 
          Real.sqrt_nonneg (a * b * c), 
          Real.sq_sqrt (show 0 ≤ (a * b * c : ℝ) by positivity), 
          mul_nonneg (Real.sqrt_nonneg (a * b * c)) (Real.sqrt_nonneg (a * b * c)), 
          mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1, 
          mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith), 
          mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 - c by linarith), 
          mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - c by linarith), 
          mul_pos (mul_pos ha1 hb1) hc1, 
          mul_pos (mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith)) (show 0 < 1 - c by linarith)]