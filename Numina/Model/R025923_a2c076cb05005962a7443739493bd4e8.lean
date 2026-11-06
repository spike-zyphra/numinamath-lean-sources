import Mathlib

theorem number_theory_297439 (a b c p : ℕ) (h₀ : a < b) (h₁ : b < c)
    (h₂ : a^2 + b^2 = c^2) (h₃ : Odd p) (h₄ : Nat.Prime p) :
    a^2 = (b + c) * p ↔ b + p = c := by
  constructor
  · -- Forward direction: If $a^2 = (b + c) * p$, then $b + p = c$
    intro h
    have h₆ : (b + c) * p = (c - b) * (b + c) := by
      have h₈ : a^2 + b^2 = c^2 := h₂
      have h₉ : a^2 = (b + c) * p := h
      have eq1 : (b + c) * p = c^2 - b^2 := by
        omega
      have h₁₀ : c ≥ b := by
        omega
      have h₇ : c^2 - b^2 = (c - b) * (c + b) := by
        have h₁₁ : c ≥ b := by
          omega
        rw [Nat.sub_mul]
        ring_nf
        all_goals omega
      have h₁₂ : (c + b) = (b + c) := by
        omega
      rw [h₁₂] at h₇
      omega
    have h₇ : p = c - b := by
      have h₉ : (b + c) * p = (c - b) * (b + c) := h₆
      have h₁₀ : b + c ≠ 0 := by
        omega
      have h₁₁ : p = c - b := by
        apply (mul_left_inj' h₁₀).mp
        linarith
      omega
    have h₈ : b + p = c := by
      omega
    omega
  · -- Backward direction: If $b + p = c$, then $a^2 = (b + c) * p$
    intro h
    have h₅ : b + p = c := h
    have h₆ : c = b + p := by
      omega
    have h₇ : a^2 + b^2 = c^2 := h₂
    have h₈ : a^2 + b^2 = (b + p) ^ 2 := by
      rw [show c = b + p by omega] at h₇
      all_goals
      linarith
    have h₉ : a^2 = p * (2 * b + p) := by
      nlinarith
    have h₆ : b + c = 2 * b + p := by
      have h₆ : c = b + p := by
        omega
      omega
    have h₇ : a^2 = (b + c) * p := by
      rw [h₆]
      linarith
    linarith