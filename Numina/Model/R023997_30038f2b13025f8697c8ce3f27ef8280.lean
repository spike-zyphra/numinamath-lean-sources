import Mathlib

theorem number_theory_205451 {a b c d : ℕ} (h₀ : a = 47) (h₁ : b ≠ 0) (h₂ : c = a / b)
    (h₃ : d = a % b) (h₄ : c = d) :
    b = 46 ∧ d = 1 := by
  rw [h₀] at h₂ h₃
  have h5 : c = 47 / b := h₂
  have h6 : d = 47 % b := h₃
  have h8 : 47 / b = 47 % b := by
    have h₄' : c = d := h₄
    rw [h5, h6] at h₄'
    exact h₄'

  have h9 : b ≤ 47 := by
    by_contra h
    push_neg at h
    have h10 : 47 / b = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    have h11 : 47 % b = 47 := by
      rw [Nat.mod_eq_of_lt]
      linarith
    have h12 : 0 = 47 := by
      have h13 : 47 / b = 47 % b := h8
      rw [h10, h11] at h13
      omega
    all_goals linarith

  interval_cases b <;> norm_num [Nat.div_eq_zero_iff, Nat.mod_eq_of_lt] at h8 ⊢
  <;> omega