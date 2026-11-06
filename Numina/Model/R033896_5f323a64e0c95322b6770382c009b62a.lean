import Mathlib

theorem inequalities_121630 (a : Fin 5 → ℝ) (ha : ∀ i, 1 < a i) :
    16 * (a 0 * a 1 * a 2 * a 3 * a 4 + 1) >
    (1 + a 0) * (1 + a 1) * (1 + a 2) * (1 + a 3) * (1 + a 4) := by 
  have ha1 : 0 < a 0 - 1 := by linarith [ha 0]
  have ha2 : 0 < a 1 - 1 := by linarith [ha 1]
  have ha3 : 0 < a 2 - 1 := by linarith [ha 2]
  have ha4 : 0 < a 3 - 1 := by linarith [ha 3]
  have ha5 : 0 < a 4 - 1 := by linarith [ha 4]
  have ha1' : 0 < a 0 := by linarith
  have ha2' : 0 < a 1 := by linarith
  have ha3' : 0 < a 2 := by linarith
  have ha4' : 0 < a 3 := by linarith
  have ha5' : 0 < a 4 := by linarith 
  nlinarith [mul_pos ha1' ha2', mul_pos ha1' ha3', mul_pos ha1' ha4', mul_pos ha1' ha5', 
          mul_pos ha2' ha3', mul_pos ha2' ha4', mul_pos ha2' ha5', 
          mul_pos ha3' ha4', mul_pos ha3' ha5', mul_pos ha4' ha5', 
          mul_pos (show 0 < (a 0 - 1) by linarith [ha 0]) 
          (show 0 < (a 1 - 1) by linarith [ha 1]), 
          mul_pos (show 0 < (a 0 - 1) by linarith [ha 0]) 
          (show 0 < (a 2 - 1) by linarith [ha 2]), 
          mul_pos (show 0 < (a 0 - 1) by linarith [ha 0]) 
          (show 0 < (a 3 - 1) by linarith [ha 3]), 
          mul_pos (show 0 < (a 0 - 1) by linarith [ha 0]) 
          (show 0 < (a 4 - 1) by linarith [ha 4]), 
          mul_pos (show 0 < (a 1 - 1) by linarith [ha 1]) 
          (show 0 < (a 2 - 1) by linarith [ha 2]), 
          mul_pos (show 0 < (a 1 - 1) by linarith [ha 1]) 
          (show 0 < (a 3 - 1) by linarith [ha 3]), 
          mul_pos (show 0 < (a 1 - 1) by linarith [ha 1]) 
          (show 0 < (a 4 - 1) by linarith [ha 4]), 
          mul_pos (show 0 < (a 2 - 1) by linarith [ha 2]) 
          (show 0 < (a 3 - 1) by linarith [ha 3]), 
          mul_pos (show 0 < (a 2 - 1) by linarith [ha 2]) 
          (show 0 < (a 4 - 1) by linarith [ha 4]), 
          mul_pos (show 0 < (a 3 - 1) by linarith [ha 3]) 
          (show 0 < (a 4 - 1) by linarith [ha 4]), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 1 by linarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 2 by linarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 3 by linarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 4 by linarith), 
          mul_pos (show 0 < a 1 by linarith) (show 0 < a 2 by linarith), 
          mul_pos (show 0 < a 1 by linarith) (show 0 < a 3 by linarith), 
          mul_pos (show 0 < a 1 by linarith) (show 0 < a 4 by linarith), 
          mul_pos (show 0 < a 2 by linarith) (show 0 < a 3 by linarith), 
          mul_pos (show 0 < a 2 by linarith) (show 0 < a 4 by linarith), 
          mul_pos (show 0 < a 3 by linarith) (show 0 < a 4 by linarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 1 * a 2 by nlinarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 1 * a 3 by nlinarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 1 * a 4 by nlinarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 2 * a 3 by nlinarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 2 * a 4 by nlinarith), 
          mul_pos (show 0 < a 0 by linarith) (show 0 < a 3 * a 4 by nlinarith), 
          mul_pos (show 0 < a 1 by linarith) (show 0 < a 2 * a 3 by nlinarith), 
          mul_pos (show 0 < a 1 by linarith) (show 0 < a 2 * a 4 by nlinarith), 
          mul_pos (show 0 < a 1 by linarith) (show 0 < a 3 * a 4 by nlinarith), 
          mul_pos (show 0 < a 2 by linarith) (show 0 < a 3 * a 4 by nlinarith)
  ]