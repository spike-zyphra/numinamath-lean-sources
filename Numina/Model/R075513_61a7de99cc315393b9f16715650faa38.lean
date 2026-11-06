import Mathlib

theorem number_theory_294381 (a b : ℕ) (h₀ : 0 < a) (h₁ : 0 < b)
    (h₂ : a^2 + b^2 ∈ Finset.Icc 97 108) (h₃ : a^2 > b^2) (h₄ : 2 ≤ a) (h₅ : 2 ≤ b)
    (h₆ : Odd (a^2 + b^2)) :
    a^2 = 81 ∧ b^2 = 16 := by
  have h₂' : 97 ≤ a^2 + b^2 ∧ a^2 + b^2 ≤ 108 := by
    simp [Finset.mem_Icc] at h₂
    exact h₂
  have h9 : a ≤ 10 := by
    by_contra h
    push_neg at h
    have h8 : a ≥ 11 := by linarith
    have h10 : a^2 ≥ 121 := by nlinarith
    have h11 : a^2 + b^2 ≥ 121 := by linarith [show b^2 ≥ 0 by nlinarith, h10]
    have h12 : a^2 + b^2 ≤ 108 := h₂'.right
    linarith
  have h8 : b ≤ 10 := by
    by_contra h
    push_neg at h
    have h7 : b ≥ 11 := by linarith
    have h8 : b^2 ≥ 121 := by nlinarith
    have h9 : a^2 + b^2 ≥ 121 := by linarith [show a^2 ≥ 0 by nlinarith, h8]
    have h10 : a^2 + b^2 ≤ 108 := h₂'.right
    linarith
  interval_cases a <;> interval_cases b <;> norm_num [Nat.odd_iff] at h₆ h₃ h₂' ⊢ <;> omega