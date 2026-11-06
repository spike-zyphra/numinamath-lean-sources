import Mathlib

theorem algebra_313272 {m : ℤ} (h : ∃ α β : ℕ, α ≠ β ∧ α > 0 ∧ β > 0 ∧ α^2 + m * α - m + 1 = 0 ∧ β^2 + m * β - m + 1 = 0) :
    m = -5 := by
  rcases h with ⟨α, β, hneq, hα, hβ, h1, h2⟩
  have eq1 : (α : ℤ) ^ 2 + m * (α : ℤ) - m + 1 = 0 := by
    exact_mod_cast h1

  have eq2 : (β : ℤ) ^ 2 + m * (β : ℤ) - m + 1 = 0 := by
    exact_mod_cast h2

  have eq3 : (α : ℤ) ^ 2 + m * (α : ℤ) - m + 1 - ((β : ℤ) ^ 2 + m * (β : ℤ) - m + 1) = 0 := by
    linarith [eq1, eq2]

  have eq4 : ((α : ℤ) - (β : ℤ)) * ((α : ℤ) + (β : ℤ) + m) = 0 := by
    ring_nf at eq3 ⊢
    nlinarith

  cases' (mul_eq_zero.mp eq4) with h3 h4
  · -- h3 : (α : ℤ) - (β : ℤ) = 0
    exfalso
    have h3' : (α : ℤ) = (β : ℤ) := by linarith
    have hneq' : α = β := by exact_mod_cast h3'
    contradiction
  · -- h4 : (α : ℤ) + (β : ℤ) + m = 0
    have hm : m = -((α : ℤ) + (β : ℤ)) := by linarith
    rw [hm] at eq1
    have h_eq1 : (α : ℤ) * (β : ℤ) = (α : ℤ) + (β : ℤ) + 1 := by
      nlinarith

    have h31 : (α : ℤ) * (β : ℤ) = (α : ℤ) + (β : ℤ) + 1 := by
      exact_mod_cast h_eq1

    have h311 : α ≤ 4 := by
      by_contra h312
      push_neg at h312
      have h313 : β ≤ 4 := by
        by_contra h314
        push_neg at h314
        have eq8 : (α : ℤ) * (β : ℤ) > (α : ℤ) + (β : ℤ) + 1 := by
          nlinarith [show (α : ℤ) ≥ 5 by omega, show (β : ℤ) ≥ 5 by omega]
        nlinarith [show (α : ℤ) * (β : ℤ) = (α : ℤ) + (β : ℤ) + 1 by linarith [h_eq1]]
      interval_cases β <;> omega

    have h312 : β ≤ 4 := by
      by_contra h313
      push_neg at h313
      have h314 : (α : ℤ) ≤ 4 := by
        by_contra h315
        push_neg at h315
        have eq8 : (α : ℤ) * (β : ℤ) > (α : ℤ) + (β : ℤ) + 1 := by
          nlinarith [show (α : ℤ) ≥ 5 by omega, show (β : ℤ) ≥ 5 by omega]
        nlinarith [show (α : ℤ) * (β : ℤ) = (α : ℤ) + (β : ℤ) + 1 by linarith [h_eq1]]
      interval_cases α <;> omega

    interval_cases α <;> interval_cases β
      <;> omega