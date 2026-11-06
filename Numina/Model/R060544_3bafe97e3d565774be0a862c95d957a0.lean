import Mathlib

theorem algebra_280221 {f : ℝ → ℝ} (hf : f = fun x => x^3 - 3 * x^2 + 6 * x - 6)
    (a b : ℝ) (ha : f a = 1) (hb : f b = -5) : a + b = 2 := by
  have h1 : a^3 - 3 * a^2 + 6 * a - 6 = 1 := by 
    rw [hf] at ha
    simpa using ha
  have eq1 : a^3 - 3 * a^2 + 6 * a - 7 = 0 := by linarith
  have h2 : b^3 - 3 * b^2 + 6 * b - 6 = -5 := by 
    rw [hf] at hb
    simpa using hb
  have eq2 : b^3 - 3 * b^2 + 6 * b - 1 = 0 := by linarith
  -- We need to show $a + b = 2$ by showing that $b = 2 - a$
  have h3 : b = 2 - a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - 2), sq_nonneg (b - 2), eq1, eq2]
  linarith [h3]