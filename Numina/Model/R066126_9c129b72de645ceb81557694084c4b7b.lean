import Mathlib

theorem algebra_10738 {f : ℝ → ℝ} (hf : f = fun x => x ^ 3 + 3 * x ^ 2 + 6 * x + 14)
    (a b : ℝ) (ha : f a = 1) (hb : f b = 19) : a + b = -2 := by
  have h1 : a ^ 3 + 3 * a ^ 2 + 6 * a + 14 = 1 := by
    rw [hf] at ha
    simpa using ha
  have h2 : b ^ 3 + 3 * b ^ 2 + 6 * b + 14 = 19 := by
    rw [hf] at hb
    simpa using hb
  have eq1 : a ^ 3 + 3 * a ^ 2 + 6 * a + 13 = 0 := by linarith
  have eq2 : b ^ 3 + 3 * b ^ 2 + 6 * b - 5 = 0 := by linarith
  have h3 : b = -2 - a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 2), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b - 1)]
  linarith