import Mathlib

theorem algebra_5027 {a b : ℝ} (h1 : a^2 + b^2 = 74) (h2 : a^3 + b^3 = 218) : a + b = 2 := by

  have eq1 : (a + b) ^ 2 = 74 + 2 * (a * b) := by
    nlinarith

  have eq2 : a^3 + b^3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by 
    ring

  rw [eq2] at h2

  have h3 : (a + b - 2) * ((a + b) ^ 2 + 2 * (a + b) - 218) = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a * b), 
              sq_nonneg (a - 2), sq_nonneg (b - 2)]

  cases' (mul_eq_zero.1 h3) with h4 h5

  · -- case where $a + b - 2 = 0$, so $a + b = 2$
    linarith

  · -- case where $(a + b)^2 + 2(a + b) - 218 = 0$ 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a * b), 
              sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a + b + 1)]