import Mathlib

theorem algebra_272719 {a b : ℝ} (f : ℝ → ℝ) (h₁ : ∀ x, f x = a * x + b)
    (h₂ : ∀ x, f (b * x + a) = x) : a + b = -2 := by
  have eq1 := h₂ 0
  rw [h₁] at eq1
  have eq2 := h₂ 1
  rw [h₁] at eq2
  have eq3 := h₂ 2
  rw [h₁] at eq3
  simp at eq1 eq2 eq3
  have eq4 : a * b = 1 := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have eq5 : a ^ 2 + b = 0 := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have h3 : b = -a^2 := by
    linarith
  rw [h3] at eq4
  have h4 : a = -1 := by
    have : a^3 = -1 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have : a = -1 := by
      have h5 : a^3 + 1 = 0 := by linarith
      have h6 : (a + 1) * (a^2 - a + 1) = 0 := by
        ring_nf at h5 ⊢
        linarith
      have h7 : a^2 - a + 1 > 0 := by
        nlinarith [sq_nonneg (a - 1 / 2)]
      have h8 : a + 1 = 0 := by 
        nlinarith
      linarith
    linarith
  have h5 : b = -1 := by
    rw [h4] at h3
    nlinarith
  linarith [h4, h5]