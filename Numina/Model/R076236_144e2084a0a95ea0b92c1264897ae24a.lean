import Mathlib

theorem algebra_128815 (t : ℝ) (ht : t ≥ 0) (x y : ℝ)
    (h1 : y = t * x + 1) (h2 : y = -x + 2 * t) :
    x ≤ 2 := by
  have h_eq1 : t * x + 1 = -x + 2 * t := by 
    rw [← h1, ← h2]
  have h_eq2 : x * (t + 1) = 2 * t - 1 := by
    linarith [h_eq1]
  nlinarith [sq_nonneg (x - 2), sq_nonneg (t + 1), sq_nonneg (x * (t + 1)), sq_nonneg (x - 2), sq_nonneg (t + 1)]