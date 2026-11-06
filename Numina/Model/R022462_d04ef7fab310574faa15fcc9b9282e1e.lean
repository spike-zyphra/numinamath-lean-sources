import Mathlib

theorem inequalities_67312 (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 2 + 1) ^ 6 / 2 ^ 7 + 1 / 2 ≥ x ^ 5 - x ^ 3 + x := by
  have h1 : (x ^ 2 + 1) ^ 6 / 2 ^ 7 + 1 / 2 - (x ^ 5 - x ^ 3 + x) ≥ 0 := by
    have h2 : (x ^ 2 + 1) ^ 6 / 2 ^ 7 + 1 / 2 - (x ^ 5 - x ^ 3 + x) =
        ((x ^ 2 + 1) ^ 6 + 64 - 128 * (x ^ 5 - x ^ 3 + x) ) / 128 := by
      ring_nf
    rw [h2] at *
    have h3 : (x ^ 2 + 1) ^ 6 + 64 - 128 * (x ^ 5 - x ^ 3 + x) ≥ 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1),
          sq_nonneg (x ^ 3 - x), sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 + x), 
          sq_nonneg ((x ^ 2 - 1) * (x ^ 2 + 1)), sq_nonneg ((x - 1) * (x + 1) * (x ^ 2 + 1)), 
          sq_nonneg ((x ^ 2 - 1) * x), sq_nonneg ((x - 1) * x), sq_nonneg ((x + 1) * x), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x ^ 2 by positivity), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x ^ 2 - x + 1 by nlinarith [sq_nonneg (x - 1 / 2), hx]), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x ^ 2 + 1 by positivity)]
    apply div_nonneg
    linarith [h3]
    all_goals norm_num
  linarith