import Mathlib

theorem algebra_236792 {f g : ℝ → ℝ}
    (hf : f = fun x => 1 - x - 4 * x ^ 2 + x ^ 4)
    (hg : g = fun x => 16 - 8 * x - 16 * x ^ 2 + x ^ 4)
    (x₁ x₂ : ℝ)
    (hx₁ : f x₁ = 0) (hx₂ : g x₂ = 0)
    (hroots : ∀ x, f x = 0 → x ≤ x₁) (hroots' : ∀ x, g x = 0 → x ≤ x₂) :
    x₁ / x₂ = 0.5 := by

  have eq1 : f x₁ = 1 - x₁ - 4 * x₁ ^ 2 + x₁ ^ 4 := by 
    rw [hf]

  have h1 : 1 - x₁ - 4 * x₁ ^ 2 + x₁ ^ 4 = 0 := by
    simpa [eq1] using hx₁

  have h2x₁ : g (2 * x₁) = 0 := by
    rw [hg]
    simp
    nlinarith [sq_nonneg (x₁ ^ 2), sq_nonneg (x₁ - 1), sq_nonneg (x₁ + 1), sq_nonneg (x₁ * (x₁ * (x₁ * (x₁ - 1)))), h1]

  have h3 : 2 * x₁ ≤ x₂ := by 
    apply hroots' (2 * x₁) 
    exact h2x₁

  have hx₂2 : f (x₂ / 2) = 0 := by 
    have h2 : g x₂ = 16 - 8 * x₂ - 16 * x₂ ^ 2 + x₂ ^ 4 := by 
      rw [hg]

    have h2_root : 16 - 8 * x₂ - 16 * x₂ ^ 2 + x₂ ^ 4 = 0 := by 
      simpa [h2] using hx₂

    have eq2 : f (x₂ / 2) = 1 - (x₂ / 2) - 4 * (x₂ / 2) ^ 2 + (x₂ / 2) ^ 4 := by 
      rw [hf]

    rw [eq2]
    nlinarith

  have h4 : x₂ / 2 ≤ x₁ := by 
    apply hroots (x₂ / 2) 
    exact hx₂2

  have h5 : x₂ ≤ 2 * x₁ := by 
    linarith

  have hx1n0 : x₁ ≠ 0 := by
    by_contra h
    rw [h] at h1
    nlinarith

  have hx2n0 : x₂ ≠ 0 := by
    by_contra h
    rw [h] at h3
    nlinarith

  have h6 : x₁ = 0.5 * x₂ := by
    nlinarith

  rw [h6]
  field_simp [hx2n0]
  <;> nlinarith