import Mathlib

theorem algebra_308438 (a b c : ℝ) (ha : a < b) (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 2 + b * x + c)
    (h : ∀ x, f x ≥ 0) :
    (a + b + c) / (b - a) ≥ 3 := by

  have h1 := h 1
  have h2 := h (-2)
  simp [hf] at h1 h2

  have h3 : a + b + c ≥ 3 * (b - a) := by
    nlinarith [sq_nonneg (a * 1 ^ 2 + b * 1 + c), sq_nonneg (a * (-2) ^ 2 + b * (-2) + c), sq_nonneg (a * (2:ℝ)^2 + b * (2:ℝ) + c), sq_nonneg (b - 2 * a)]

  have h4 : b - a > 0 := by linarith

  apply (le_div_iff₀ (by linarith)).mpr
  linarith