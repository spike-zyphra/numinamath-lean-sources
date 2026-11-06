import Mathlib

theorem algebra_22027 {a b : ℝ} (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x + b)
    (h₁ : ∀ x, f (f (f x)) = 8 * x + 21) : a + b = 5 := by
  have h2 := h₁ 0
  simp [h₀] at h2
  have h3 := h₁ 1
  simp [h₀] at h3
  have eq1 : a ^ 3 = 8 := by
    nlinarith
  have ha : a = 2 := by
    have h_eq : a ^ 3 - 8 = 0 := by linarith
    have factorization : (a - 2) * (a ^ 2 + 2 * a + 4) = 0 := by 
      ring_nf at h_eq ⊢ 
      linarith 
    cases' (mul_eq_zero.1 factorization) with h_a h_b 
    · linarith
    · have discriminant_neg : (a + 1)^2 + 3 = 0 := by 
        nlinarith
      have h_nonneg : (a + 1)^2 ≥ 0 := sq_nonneg (a + 1)
      nlinarith 
  have hb : b = 3 := by 
    rw [ha] at h2
    nlinarith
  rw [ha, hb]
  all_goals norm_num 
  all_goals linarith