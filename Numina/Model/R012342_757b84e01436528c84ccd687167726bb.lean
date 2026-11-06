import Mathlib

theorem algebra_235247 {f g : ℝ → ℝ}
    (hf : f = fun x => 1 - x - 4 * x ^ 2 + x ^ 4)
    (hg : g = fun x => 16 - 8 * x - 16 * x ^ 2 + x ^ 4)
    (x₁ x₂ : ℝ)
    (hx₁ : f x₁ = 0) (hx₂ : g x₂ = 0)
    (hmax₁ : ∀ x, f x = 0 → x ≤ x₁) (hmax₂ : ∀ x, g x = 0 → x ≤ x₂) :
    x₂ / x₁ = 2 := by

  have f_eq : ∀ x, f x = 1 - x - 4 * x ^ 2 + x ^ 4 := by
    intro x
    rw [hf]

  have g_eq : ∀ x, g x = 16 - 8 * x - 16 * x ^ 2 + x ^ 4 := by
    intro x
    rw [hg]

  have h1 : g (2 * x₁) = 0 := by
    calc
      g (2 * x₁) = 16 - 8 * (2 * x₁) - 16 * (2 * x₁) ^ 2 + (2 * x₁) ^ 4 := by
        rw [g_eq]
      _ = 16 * (1 - x₁ - 4 * x₁ ^ 2 + x₁ ^ 4) := by
        ring_nf
      _ = 16 * (f x₁) := by
        rw [f_eq]
      _ = 0 := by
        rw [hx₁]
        norm_num

  have h2 : x₂ ≥ 2 * x₁ := by
    have h3 : g (2 * x₁) = 0 := h1
    have h4 : (2 * x₁) ≤ x₂ := by
      apply hmax₂
      exact h3
    linarith

  have h3 : f (x₂ / 2) = 0 := by
    have h4 : g x₂ = 0 := hx₂
    have eq1 : 1 - (x₂ / 2) - 4 * (x₂ / 2) ^ 2 + (x₂ / 2) ^ 4 = (16 - 8 * x₂ - 16 * x₂ ^ 2 + x₂ ^ 4) / 16 := by
      ring_nf
    calc
      f (x₂ / 2) = 1 - (x₂ / 2) - 4 * (x₂ / 2) ^ 2 + (x₂ / 2) ^ 4 := by
        rw [f_eq]
      _ = (16 - 8 * x₂ - 16 * x₂ ^ 2 + x₂ ^ 4) / 16 := by
        rw [eq1]
      _ = (0) / 16 := by
        have eq2 : 16 - 8 * x₂ - 16 * x₂ ^ 2 + x₂ ^ 4 = 0 := by
          rw [g_eq] at h4
          linarith
        rw [eq2]
      _ = 0 := by
        norm_num

  have h4 : x₂ / 2 ≤ x₁ := by
    apply hmax₁
    exact h3

  have h5 : x₂ = 2 * x₁ := by
    linarith [h2, h4]

  have h6 : x₁ ≠ 0 := by
    by_contra h
    have h7 : x₁ = (0 : ℝ) := by linarith
    have h8 : f x₁ = 0 := hx₁
    rw [h7] at h8
    norm_num [f_eq] at h8

  rw [show x₂ = 2 * x₁ by linarith [h5]]
  field_simp [h6]
  <;> nlinarith