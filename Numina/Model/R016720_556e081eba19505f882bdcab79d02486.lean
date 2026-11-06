import Mathlib

theorem inequalities_41465 (a b c A B C k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hk : 0 < k) (h1 : a + A = k) (h2 : b + B = k)
    (h3 : c + C = k) : a * B + b * C + c * A ≤ k ^ 2 := by
  have hA' : A = k - a := by linarith 
  have hB' : B = k - b := by linarith 
  have hC' : C = k - c := by linarith 
  rw [hA', hB', hC']
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (k - a - b), sq_nonneg (k - a - c), sq_nonneg (k - b - c), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < k - a by nlinarith) (show 0 < k - b by nlinarith), 
            mul_pos (show 0 < k - b by nlinarith) (show 0 < k - c by nlinarith), 
            mul_pos (show 0 < k - a by nlinarith) (show 0 < k - c by nlinarith), 
            mul_pos (show 0 < k by linarith) (show 0 < k by linarith)]