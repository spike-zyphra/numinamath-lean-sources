import Mathlib

theorem inequalities_61667 (a : ℝ) (ha : a > 0) (f : ℝ → ℝ)
    (h : ∀ x₁ x₂, f x₁ + f x₂ ≥ a * f (x₁ + x₂)) :
    ∀ x₁ x₂ x₃, f x₁ + f x₂ + f x₃ ≥ (3 * a ^ 2 / (a + 2)) * f (x₁ + x₂ + x₃) := by
  intro x₁ x₂ x₃
  have h1 : f x₁ + f (x₂ + x₃) ≥ a * f (x₁ + x₂ + x₃) := by
    have h' := h x₁ (x₂ + x₃)
    ring_nf at h' ⊢
    linarith
  have h2 : f x₂ + f (x₁ + x₃) ≥ a * f (x₁ + x₂ + x₃) := by
    have h' := h x₂ (x₁ + x₃)
    ring_nf at h' ⊢
    linarith
  have h3 : f x₃ + f (x₁ + x₂) ≥ a * f (x₁ + x₂ + x₃) := by
    have h' := h x₃ (x₁ + x₂)
    ring_nf at h' ⊢
    linarith
  have h4 : f x₂ + f x₃ ≥ a * f (x₂ + x₃) := by
    have h' := h x₂ x₃
    ring_nf at h' ⊢
    linarith
  have h5 : f x₁ + f x₃ ≥ a * f (x₁ + x₃) := by
    have h' := h x₁ x₃
    ring_nf at h' ⊢
    linarith
  have h6 : f x₁ + f x₂ ≥ a * f (x₁ + x₂) := by
    have h' := h x₁ x₂
    ring_nf at h' ⊢
    linarith
  have h7 : (f x₁ + f x₂ + f x₃) * (a + 2) ≥ 3 * a ^ 2 * f (x₁ + x₂ + x₃) := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (f x₁ + f x₂ + f x₃ - f (x₁ + x₂ + x₃)), sq_nonneg (f (x₂ + x₃) + f (x₁ + x₃) + f (x₁ + x₂)), mul_pos ha (show 0 < a by linarith)]
  have h8 : f x₁ + f x₂ + f x₃ ≥ (3 * a ^ 2 / (a + 2)) * f (x₁ + x₂ + x₃) := by
    have h7' : (f x₁ + f x₂ + f x₃) * (a + 2) ≥ 3 * a ^ 2 * f (x₁ + x₂ + x₃) := h7
    have h9 : a + 2 > 0 := by linarith
    have h10 : (f x₁ + f x₂ + f x₃) ≥ (3 * a ^ 2 * f (x₁ + x₂ + x₃)) / (a + 2) := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    have h11 : (3 * a ^ 2 * f (x₁ + x₂ + x₃)) / (a + 2) = (3 * a ^ 2 / (a + 2)) * f (x₁ + x₂ + x₃) := by
      field_simp
      <;> linarith
    linarith [h11, h10]
  exact h8