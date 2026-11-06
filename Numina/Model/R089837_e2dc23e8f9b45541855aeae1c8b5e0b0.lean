import Mathlib

theorem algebra_220968 {x : ℝ} (hx : x ≠ 0) (h : x * (4 / 5) * (5 / 6) * x = x) :
    x = 1.5 := by
  have h1 : x * (4 / 5) * (5 / 6) * x - x = 0 := by linarith
  have h2 : x * (2 / 3) * x - x = 0 := by
    linarith [h1]
  have h3 : x * (x * (2 / 3) - 1) = 0 := by
    linarith [h2]
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case x = 0
    exfalso
    exact hx h4
  · -- Case x * (2/3) - 1 = 0
    have h6 : x = 3 / 2 := by
      linarith
    rw [h6]
    norm_num