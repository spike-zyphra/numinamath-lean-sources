import Mathlib

theorem inequalities_226687 (a b c : ℝ) (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) (hc : c ∈ Set.Ioo 0 1) :
    a + b + c + 2 * a * b * c > a * b + b * c + c * a + 2 * Real.sqrt (a * b * c) := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals
      linarith
  have h2 : 0 < Real.sqrt (a * b * c) := by
    apply Real.sqrt_pos.2
    nlinarith
  have h3 : Real.sqrt (a * b * c) ≥ 0 := by
    apply Real.sqrt_nonneg
  nlinarith [sq_nonneg (a + b + c - 1), sq_nonneg (a * b + b * c + c * a - a * b * c), sq_nonneg (Real.sqrt (a * b * c) - a), sq_nonneg (Real.sqrt (a * b * c) - b), sq_nonneg (Real.sqrt (a * b * c) - c), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a * b * c by positivity), 
          mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith), 
          mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 - c by linarith), 
          mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - c by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < c by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < b by linarith) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < c by linarith) (show 0 < a * b by nlinarith)
          ]