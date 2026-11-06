import Mathlib

theorem inequalities_600011 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (h : x < a) :
    (a - x)^6 - 3 * a * (a - x)^5 + 5 / 2 * a^2 * (a - x)^4 - 1 / 2 * a^4 * (a - x)^2 < 0 := by
  have h1 : 0 < a - x := by
    linarith
  have h2 : 0 < x := hx
  have h3 : 0 < a - x := by linarith
  have h4 : 0 < a := ha
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos h1, sq_pos_of_pos hx, 
          sq_pos_of_pos (show 0 < a * x by nlinarith), 
          sq_pos_of_pos (show 0 < a * (a - x) by nlinarith), 
          sq_pos_of_pos (show 0 < x * (a - x) by nlinarith), 
          mul_pos ha hx, mul_pos ha (show 0 < a - x by linarith), 
          mul_pos hx (show 0 < a - x by linarith), 
          pow_pos ha 2, pow_pos ha 3, pow_pos ha 4, 
          pow_pos h1 2, pow_pos h1 3, pow_pos h1 4, pow_pos h1 5, pow_pos h1 6, 
          mul_pos (show 0 < a * x by nlinarith) (show 0 < a - x by linarith), 
          mul_pos (show 0 < x * (a - x) by nlinarith) (show 0 < a by linarith)]