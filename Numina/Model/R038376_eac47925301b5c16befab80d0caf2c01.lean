import Mathlib

theorem algebra_9442 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 3 + x)
  (a b c : ℝ) (ha : a + b > 0) (hb : b + c > 0) (hc : c + a > 0) :
  f a + f b + f c > 0 := by
  rw [hf a, hf b, hf c]
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a + b + c), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
          mul_pos (show (0 : ℝ) < a + b by linarith) (show (0 : ℝ) < b + c by linarith), 
          mul_pos (show (0 : ℝ) < a + b by linarith) (show (0 : ℝ) < c + a by linarith), 
          mul_pos (show (0 : ℝ) < b + c by linarith) (show (0 : ℝ) < c + a by linarith)
          ]