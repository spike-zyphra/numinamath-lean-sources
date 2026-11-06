import Mathlib

theorem algebra_2264 (x : ℝ) (h : 14 * x + 5 - 21 * x ^ 2 = -2) : 6 * x ^ 2 - 4 * x + 5 = 7 := by
  have h1 : -21 * x^2 + 14 * x + 7 = 0 := by
    nlinarith
  have h2 : 21 * x^2 - 14 * x - 7 = 0 := by 
    nlinarith [h1]
  have h3 : 3 * x^2 - 2 * x - 1 = 0 := by
    nlinarith [h2]
  have factored : (3 * x + 1) * (x - 1) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp factored) with h4 h5
  · -- Case $3x + 1 = 0$, so $x = -1/3$
    have hx : x = -1 / 3 := by
      linarith
    rw [hx]
    norm_num
  · -- Case $x - 1 = 0$, so $x = 1$
    have hx : x = 1 := by
      linarith
    rw [hx]
    norm_num