import Mathlib

theorem inequalities_278976 (a b c A B C k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (h : a + A = k) (h' : b + B = k) (h'' : c + C = k) :
    a * B + b * C + c * A ≤ k ^ 2 := by
  have h1 : A = k - a := by linarith
  have h2 : B = k - b := by linarith
  have h3 : C = k - c := by linarith
  rw [h1] at *
  rw [h2] at *
  rw [h3] at *
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (k - a - b), sq_nonneg (k - b - c), sq_nonneg (k - c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < k - a by nlinarith) (show 0 < k - b by nlinarith), 
          mul_pos (show 0 < k - b by nlinarith) (show 0 < k - c by nlinarith), 
          mul_pos (show 0 < k - a by nlinarith) (show 0 < k - c by nlinarith)
        ]