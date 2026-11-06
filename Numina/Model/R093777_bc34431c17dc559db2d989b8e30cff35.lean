import Mathlib

theorem algebra_325287 {f : ℝ → ℝ} (hf : f = fun x => x^3 - 6 * x^2 + 17 * x - 5)
    (a b : ℝ) (ha : f a = 3) (hb : f b = 23) : a + b = 4 := by
  have h1 : a ^ 3 - 6 * a^2 + 17 * a - 5 = 3 := by
    rw [hf] at ha
    exact_mod_cast ha
  have h2 : b ^ 3 - 6 * b^2 + 17 * b - 5 = 23 := by
    rw [hf] at hb
    exact_mod_cast hb
  have h3 : a^3 - 6 * a^2 + 17 * a - 8 = 0 := by linarith
  have h4 : b^3 - 6 * b^2 + 17 * b - 28 = 0 := by linarith
  have h5 : a + b = 4 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2), sq_nonneg (b - 2),
              sq_nonneg (a + b - 4)]
  exact h5