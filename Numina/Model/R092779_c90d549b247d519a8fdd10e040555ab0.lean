import Mathlib

theorem inequalities_92120 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y = 2) :
    x ^ 2 * y ^ 2 * (x ^ 2 + y ^ 2) ≤ 2 := by
  have h1 : y = 2 - x := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x * (x - 1)), sq_nonneg ((2 - x) * ((2 - x) - 1)), sq_nonneg (x * (x - (2 - x))), sq_nonneg (x * ((2 - x) - 1)), 
          sq_nonneg (x * (2 - x)), 
          sq_nonneg ((x - 1)^2), 
          sq_nonneg ((2 - x) - 1), 
          mul_nonneg (show 0 ≤ x from by linarith) (show 0 ≤ (2 - x) from by nlinarith), 
          mul_nonneg (show 0 ≤ (x) from by linarith) (show 0 ≤ (x) from by linarith), 
          mul_nonneg (show 0 ≤ (2 - x) from by nlinarith) (show 0 ≤ (2 - x) from by nlinarith),
          sq_nonneg (x^2 + (2 - x) ^ 2 - 2), sq_nonneg (x * (2 - x) - 1)]
  all_goals nlinarith [sq_nonneg (x * (x - 1)), sq_nonneg ((2 - x) * ((2 - x) - 1)), sq_nonneg (x * (x - (2 - x))), sq_nonneg (x * ((2 - x) - 1)), 
          sq_nonneg (x * (2 - x)), 
          sq_nonneg ((x - 1)^2), 
          sq_nonneg ((2 - x) - 1), 
          mul_nonneg (show 0 ≤ x from by linarith) (show 0 ≤ (2 - x) from by nlinarith), 
          mul_nonneg (show 0 ≤ (x) from by linarith) (show 0 ≤ (x) from by linarith), 
          mul_nonneg (show 0 ≤ (2 - x) from by nlinarith) (show 0 ≤ (2 - x) from by nlinarith),
          sq_nonneg (x^2 + (2 - x) ^ 2 - 2), sq_nonneg (x * (2 - x) - 1)]
  all_goals nlinarith [sq_nonneg (x * (x - 1)), sq_nonneg ((2 - x) * ((2 - x) - 1)), sq_nonneg (x * (x - (2 - x))), sq_nonneg (x * ((2 - x) - 1)), 
          sq_nonneg (x * (2 - x)), 
          sq_nonneg ((x - 1)^2), 
          sq_nonneg ((2 - x) - 1), 
          mul_nonneg (show 0 ≤ x from by linarith) (show 0 ≤ (2 - x) from by nlinarith), 
          mul_nonneg (show 0 ≤ (x) from by linarith) (show 0 ≤ (x) from by linarith), 
          mul_nonneg (show 0 ≤ (2 - x) from by nlinarith) (show 0 ≤ (2 - x) from by nlinarith),
          sq_nonneg (x^2 + (2 - x) ^ 2 - 2), sq_nonneg (x * (2 - x) - 1)]
  all_goals nlinarith [sq_nonneg (x * (x - 1)), sq_nonneg ((2 - x) * ((2 - x) - 1)), sq_nonneg (x * (x - (2 - x))), sq_nonneg (x * ((2 - x) - 1)), 
          sq_nonneg (x * (2 - x)), 
          sq_nonneg ((x - 1)^2), 
          sq_nonneg ((2 - x) - 1), 
          mul_nonneg (show 0 ≤ x from by linarith) (show 0 ≤ (2 - x) from by nlinarith), 
          mul_nonneg (show 0 ≤ (x) from by linarith) (show 0 ≤ (x) from by linarith), 
          mul_nonneg (show 0 ≤ (2 - x) from by nlinarith) (show 0 ≤ (2 - x) from by nlinarith),
          sq_nonneg (x^2 + (2 - x) ^ 2 - 2), sq_nonneg (x * (2 - x) - 1)]
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith