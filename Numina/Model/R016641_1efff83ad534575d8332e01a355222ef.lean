import Mathlib

theorem inequalities_597788 (a b c : ℝ) (ha : -2 < a) (hb : -2 < b) (hc : -2 < c)
    (h1 : a < 1) (h2 : b < 1) (h3 : c < 1) :
    a * b * c > a + b + c - 2 := by
  have h4 : 0 < 1 - a := by linarith
  have h5 : 0 < 1 - b := by linarith
  have h6 : 0 < 1 - c := by linarith
  have h7 : 0 < a + 2 := by linarith
  have h8 : 0 < b + 2 := by linarith
  have h9 : 0 < c + 2 := by linarith
  nlinarith [mul_pos (show (0 : ℝ) < 1 - a by linarith) (show (0 : ℝ) < 1 - b by linarith), 
            mul_pos (show (0 : ℝ) < 1 - b by linarith) (show (0 : ℝ) < 1 - c by linarith), 
            mul_pos (show (0 : ℝ) < 1 - a by linarith) (show (0 : ℝ) < 1 - c by linarith), 
            mul_pos (show (0 : ℝ) < a + 2 by linarith) (show (0 : ℝ) < b + 2 by linarith), 
            mul_pos (show (0 : ℝ) < b + 2 by linarith) (show (0 : ℝ) < c + 2 by linarith), 
            mul_pos (show (0 : ℝ) < a + 2 by linarith) (show (0 : ℝ) < c + 2 by linarith), 
            mul_pos (show (0 : ℝ) < 1 - a by linarith) (show (0 : ℝ) < a + 2 by linarith), 
            mul_pos (show (0 : ℝ) < 1 - b by linarith) (show (0 : ℝ) < b + 2 by linarith), 
            mul_pos (show (0 : ℝ) < 1 - c by linarith) (show (0 : ℝ) < c + 2 by linarith)
          ]