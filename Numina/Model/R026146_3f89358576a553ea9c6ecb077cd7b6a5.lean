import Mathlib

open Real

theorem calculus_245492 (f g : ℝ → ℝ)
    (hf : f = fun x => 1000 * x) (hg : g = fun x => x ^ 2 / 1000) :
    ∀ x, 0 < x → (x < 500000 → deriv f x > deriv g x) ∧ (x > 500000 → deriv g x > deriv f x) := by
  intro x hx
  have hf_eq : f = fun x => 1000 * x := hf
  have hg_eq : g = fun x => x ^ 2 / 1000 := hg
  have hfderiv : ∀ x, deriv f x = 1000 := by
    intro x
    rw [hf_eq]
    simp [deriv_mul, deriv_id', mul_comm]
    all_goals linarith
  have hgderiv : ∀ x, deriv g x = (2 * x) / 1000 := by
    intro x
    rw [hg_eq]
    simp [deriv_div_const, deriv_pow, deriv_const]
    all_goals linarith
  constructor
  · -- First part: if x < 500000, then deriv f x > deriv g x
    intro h1
    have h2 : deriv f x = 1000 := hfderiv x
    have h4 : deriv g x = (2 * x) / 1000 := hgderiv x
    rw [h2, h4]
    have h5 : x < 500000 := h1
    linarith
  · -- Second part: if x > 500000, then deriv g x > deriv f x
    intro h2
    have h4 : deriv f x = 1000 := hfderiv x
    have h5 : deriv g x = (2 * x) / 1000 := hgderiv x
    rw [h4, h5]
    have h6 : x > 500000 := h2
    linarith