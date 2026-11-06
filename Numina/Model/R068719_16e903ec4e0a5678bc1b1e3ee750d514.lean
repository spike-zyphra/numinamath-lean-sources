import Mathlib

theorem number_theory_179375 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h : y^2 - x * (x + 1) * (x + 2) * (x + 3) = 1) :
    y = x^2 + 3 * x + 1 := by
  have eq1 : (y : ℕ) ^ 2 = x * (x + 1) * (x + 2) * (x + 3) + 1 := by 
    omega
  have eq2 : (y : ℕ) ^ 2 = (x^2 + 3 * x + 1 : ℕ) ^ 2 := by
    nlinarith [eq1, sq_nonneg (x^2 + 3 * x + 1), sq_nonneg (y - (x^2 + 3 * x + 1)), sq_nonneg (y + (x^2 + 3 * x + 1)), mul_pos (show 0 < x by linarith) (show 0 < x + 1 by linarith), mul_pos (show 0 < x + 1 by linarith) (show 0 < x + 2 by linarith), mul_pos (show 0 < x + 2 by linarith) (show 0 < x + 3 by linarith)]
  have h_eq : (y : ℕ) = (x^2 + 3 * x + 1 : ℕ) := by
    nlinarith [sq_nonneg (y : ℕ), sq_nonneg (x^2 + 3 * x + 1 : ℕ), eq2, sq_nonneg (y - (x^2 + 3 * x + 1)), sq_nonneg (y + (x^2 + 3 * x + 1)), mul_pos (show 0 < x by linarith) (show 0 < x + 1 by linarith), mul_pos (show 0 < x + 1 by linarith) (show 0 < x + 2 by linarith), mul_pos (show 0 < x + 2 by linarith) (show 0 < x + 3 by linarith)]
  omega