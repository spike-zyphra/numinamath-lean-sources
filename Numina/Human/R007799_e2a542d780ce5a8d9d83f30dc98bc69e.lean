import Mathlib

theorem algebra_13490 {x : ℝ} (hx : x ≥ 0) (h : Real.sqrt x = x - 72) :
    x = 81 := by
  have h1 : x = (x - 72) ^ 2 := by
    calc
      x = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt hx]
      _ = (x - 72) ^ 2 := by rw [h]
  have : x ^ 2 - 145 * x + 5184 = 0 := by linarith [h1]
  have : (x - 81) * (x - 64) = 0 := by linarith
  cases' (mul_eq_zero.mp this) with h2 h3
  linarith
  exfalso
  have : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
  linarith