import Mathlib

theorem algebra_207913 {f : ℝ → ℝ} (hf : f = fun x => x^3 + 3 * x^2 + 6 * x + 14) (a b : ℝ)
    (ha : f a = 1) (hb : f b = 19) : a + b = -2 := by 
  have eq1 : a^3 + 3 * a^2 + 6 * a + 14 = 1 := by 
    rw [hf] at ha
    simp at ha ⊢
    linarith
  have eq2 : b^3 + 3 * b^2 + 6 * b + 14 = 19 := by 
    rw [hf] at hb
    simp at hb ⊢
    linarith
  have eq3 : a^3 + 3 * a^2 + 6 * a + 13 = 0 := by linarith
  have eq4 : b^3 + 3 * b^2 + 6 * b - 5 = 0 := by linarith

  -- solving complex equations using nonnegativity
  have h1 : b = -2 - a := by
    nlinarith [sq_nonneg (a + b + 2), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a + 2)]
    -- also can to be used
    <;> nlinarith [sq_nonneg (a + b + 2), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a + b + 2), sq_nonneg (a + 2)]
  nlinarith [h1]