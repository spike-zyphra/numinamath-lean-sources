import Mathlib

theorem algebra_231582 {f g φ : ℝ → ℝ} (hfg : ∀ x y, x ≠ y → (f x - g y) / (x - y) = φ ((x + y) / 2)) :
    ∀ x y, x ≠ y → f x - g y = φ ((x + y) / 2) * (x - y) := by
  intro x y hxy
  have h := hfg x y hxy
  have h2 : x - y ≠ 0 := by
    intro h3
    apply hxy
    linarith
  field_simp [h2] at h ⊢
  <;> linarith