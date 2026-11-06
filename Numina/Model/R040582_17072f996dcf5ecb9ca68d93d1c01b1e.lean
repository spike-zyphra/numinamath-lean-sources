import Mathlib

theorem inequalities_269414 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b) * (a ^ 4 + b ^ 4) ≥ (a ^ 2 + b ^ 2) * (a ^ 3 + b ^ 3) := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
          sq_nonneg (a * b), mul_pos ha hb, sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + b), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)]