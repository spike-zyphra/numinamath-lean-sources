import Mathlib

theorem algebra_180946 {θ : ℝ} (hθ : 0 < θ ∧ θ < Real.pi) (x : ℝ) (hx : x ≠ 0)
    (h : x + 1/x = 2 * Real.cos θ) (n : ℕ) :
    x ^ n + 1 / x ^ n = 2 * Real.cos (n * θ) := by
  have h1 : x ^ 2 - 2 * Real.cos θ * x + 1 = 0 := by
    have h1 := h 
    field_simp at h1 
    nlinarith
  have h2 : (2 * Real.cos θ) ^ 2 - 4 < (0 : ℝ) := by
    nlinarith [Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2, Real.cos_sq_add_sin_sq θ]
  have h3 : x ^ 2 - 2 * Real.cos θ * x + 1 = 0 := h1 
  nlinarith [sq_nonneg ((x - Real.cos θ) ), sq_nonneg ((x - 1 / x) * x), 
          sq_nonneg ((x ^ 2 - 1) / x), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq θ, sq_pos_of_ne_zero hx]