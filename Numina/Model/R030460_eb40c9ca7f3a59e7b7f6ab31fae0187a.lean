import Mathlib

theorem inequalities_214962 (x y : ℝ) (hx : 1 < x) (hy : 1 < y) :
    8 ≤ x ^ 2 / (y - 1) + y ^ 2 / (x - 1) := by
  have h1 : 0 < y - 1 := by linarith
  have h2 : 0 < x - 1 := by linarith
  have h3 : x ^ 2 / (y - 1) + y ^ 2 / (x - 1) - 8 ≥ 0 := by
    have h4 : x ^ 2 / (y - 1) + y ^ 2 / (x - 1) - 8 =
        (x ^ 2 * (x - 1) + y ^ 2 * (y - 1) - 8 * ( (x - 1) * (y - 1) )) / ((y - 1) * (x - 1)) := by
      field_simp
      <;> ring
    rw [h4] at *
    have h5 : 0 < (y - 1) * (x - 1) := by
      positivity
    have h6 : x ^ 2 * (x - 1) + y ^ 2 * (y - 1) - 8 * ( (x - 1) * (y - 1) ) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2),
          sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * (x - 2) - y * (y - 2)), sq_nonneg ((x - 1) - (y - 1)), 
          mul_pos (show 0 < x - 1 by linarith) (show 0 < y - 1 by linarith), 
          mul_pos (show 0 < x - 1 by linarith) (show 0 < x - 1 by linarith), 
          mul_pos (show 0 < y - 1 by linarith) (show 0 < y - 1 by linarith), 
          mul_pos (show 0 < x - 1 by linarith) (show 0 < x by linarith), 
          mul_pos (show 0 < y - 1 by linarith) (show 0 < y by linarith)]
    apply div_nonneg
    linarith
    all_goals
      positivity
  linarith