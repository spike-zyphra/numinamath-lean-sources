import Mathlib

theorem inequalities_148958 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : a ≤ d ∧ b ≤ d ∧ c ≤ d) :
    a * (d - b) + b * (d - c) + c * (d - a) ≤ d ^ 2 := by 
  rcases hd with ⟨ha1, hb1, hc1⟩
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (d - a), sq_nonneg (d - b), sq_nonneg (d - c), 
          mul_pos ha hb, mul_pos ha hc, 
          mul_pos hb hc, 
          mul_nonneg (show 0 ≤ d - a by linarith) (show 0 ≤ d - b by linarith), 
          mul_nonneg (show 0 ≤ d - b by linarith) (show 0 ≤ d - c by linarith), 
          mul_nonneg (show 0 ≤ d - a by linarith) (show 0 ≤ d - c by linarith)]