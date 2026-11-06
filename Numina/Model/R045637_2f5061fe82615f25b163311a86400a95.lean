import Mathlib

theorem algebra_52129 {f : ℝ → ℝ → ℝ} (hf : ∀ x y, f x y = 3 * x ^ 2 + 3 * x * y + 1)
    (a b : ℝ) (ha : f a b + 1 = 42) (hb : f b a = 42) : |a + b| = 3 * Real.sqrt 3 := by

  have eq1 : f a b = 3 * a ^ 2 + 3 * a * b + 1 := by
    specialize hf a b
    simpa using hf
  have eq2 : f b a = 3 * b ^ 2 + 3 * b * a + 1 := by
    specialize hf b a 
    simpa using hf
  rw [eq1] at ha
  rw [eq2] at hb
  have eq3 : 3 * a ^ 2 + 3 * a * b = 40 := by linarith
  have eq4 : 3 * b ^ 2 + 3 * a * b = 41 := by
    nlinarith
  have h1 : 3 * (a + b) ^ 2 = 81 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b)]
  have h2 : (a + b) ^ 2 = 27 := by
    nlinarith
  have h3 : |a + b| = Real.sqrt ((a + b) ^ 2) := by 
    rw [Real.sqrt_sq_eq_abs]
  have h4 : Real.sqrt ((a + b) ^ 2) = Real.sqrt (27 : ℝ) := by 
    rw [h2]
  have h5 : Real.sqrt (27 : ℝ) = 3 * Real.sqrt 3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h3, h4, h5]
  all_goals linarith