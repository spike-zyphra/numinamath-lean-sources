import Mathlib

theorem inequalities_253425 (a b c : ℝ) (ha : a ∈ Set.Icc (-1) 2) (hb : b ∈ Set.Icc (-1) 2) (hc : c ∈ Set.Icc (-1) 2) :
    a * b * c + 4 ≥ a * b + b * c + c * a := by 
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  nlinarith [mul_nonneg (show 0 ≤ (2 - a) by linarith) (show 0 ≤ (2 - b) by linarith), 
          mul_nonneg (show 0 ≤ (2 - a) by linarith) (show 0 ≤ (2 - c) by linarith), 
          mul_nonneg (show 0 ≤ (2 - b) by linarith) (show 0 ≤ (2 - c) by linarith), 
          mul_nonneg (show 0 ≤ a + 1 by linarith) (show 0 ≤ b + 1 by linarith), 
          mul_nonneg (show 0 ≤ a + 1 by linarith) (show 0 ≤ c + 1 by linarith), 
          mul_nonneg (show 0 ≤ (b + 1) by linarith) (show 0 ≤ (c + 1) by linarith), 
          mul_nonneg (show 0 ≤ (2 - a) by linarith) (show 0 ≤ (b + 1) by linarith), 
          mul_nonneg (show 0 ≤ (2 - a) by linarith) (show 0 ≤ (c + 1) by linarith), 
          mul_nonneg (show 0 ≤ (2 - b) by linarith) (show 0 ≤ (a + 1) by linarith), 
          mul_nonneg (show 0 ≤ (2 - c) by linarith) (show 0 ≤ (b + 1) by linarith), 
          mul_nonneg (show 0 ≤ (2 - c) by linarith) (show 0 ≤ (a + 1) by linarith), 
          mul_nonneg (show 0 ≤ (a + 1) by linarith) (show 0 ≤ (2 - a) by linarith)
  ]