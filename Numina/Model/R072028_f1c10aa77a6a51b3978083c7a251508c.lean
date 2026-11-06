import Mathlib

theorem algebra_4446 {α β γ k : ℝ} (h₁ : α ≠ β) (h₂ : α ≠ γ) (h₃ : β ≠ γ)
    (h₄ : α^2 + k * α + 8 = 0) (h₅ : β^2 + k * β + 8 = 0)
    (h₆ : α^2 - α - k + 7 = 0) (h₇ : γ^2 - γ - k + 7 = 0) :
    β + γ = -6 := by
        have h₈ : (α - β) * (α + β + k) = 0 := by
            nlinarith
        have h₉ : (α - γ) * (α + γ - 1) = 0 := by
            nlinarith
        have h10 : α + β + k = 0 := by
            apply_fun (λ x => x / (α - β)) at h₈
            field_simp [sub_ne_zero.mpr h₁] at h₈
            linarith
        have h11 : α + γ = 1 := by
            apply_fun (λ x => x / (α - γ)) at h₉
            field_simp [sub_ne_zero.mpr h₂] at h₉
            linarith
        have h12 : (α + 1) * (k + 1) = 0 := by
            nlinarith [h₄, h₆]
        cases' (mul_eq_zero.mp h12) with h13 h14
        · -- Case $\alpha + 1 = 0$
            have h15 : α = -1 := by linarith
            have h16 : γ = 2 := by
                rw [h15] at h11
                linarith
            have h17 : k = 9 := by
                rw [h15] at h₄
                nlinarith
            have h18 : β = -8 := by
                rw [h15, h17] at h10
                linarith
            linarith [h16, h18]
        · -- Case $k + 1 = 0$
            have h19 : k = -1 := by linarith
            have h20 : α + β = 1 := by
                rw [h19] at h10
                linarith
            have h21 : α + γ = 1 := h11
            have h22 : β = γ := by linarith [h20, h21]
            exfalso
            exact h₃ h22