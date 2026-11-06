import Mathlib

open Real Set
open scoped Real

theorem algebra_290168 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
  (h : ∀ x, sin x ^ 4 / a + cos x ^ 4 / b = 1 / (a + b)) :
  ∀ x, sin x ^ 8 / a ^ 3 + cos x ^ 8 / b ^ 3 = 1 / (a + b) ^ 3 := by
  intro x 
  have h1 := h (Real.pi / 2)
  have h2 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have h3 : cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  rw [h2, h3] at h1 
  field_simp at h1 
  <;> nlinarith