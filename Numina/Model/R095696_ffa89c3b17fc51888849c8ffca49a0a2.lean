import Mathlib

theorem algebra_237364 {a b c : ℤ} (h₀ : a * b = -6) (h₁ : a * c = -10)
    (h₂ : b * c = 15) :
    a * b * c = 30 ∧ a = 2 ∧ b = -3 ∧ c = -5 ∨ a * b * c = -30 ∧ a = -2 ∧ b = 3 ∧ c = 5 := by
  have h3 : (a * b * c) ^ 2 = 900 := by
    calc
      (a * b * c) ^ 2 = (a * b) * (a * c) * (b * c) := by ring
      _ = (-6) * (-10) * (15) := by rw [h₀, h₁, h₂]
      _ = 900 := by norm_num
  have h4 : a * b * c = 30 ∨ a * b * c = -30 := by
    have h5 : (a * b * c) ^ 2 = 900 := h3
    have h6 : (a * b * c) ^ 2 - 900 = 0 := by linarith
    have h7 : ((a * b * c) - 30) * ((a * b * c) + 30) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h7) with
    | inl h8 =>
      left
      linarith
    | inr h9 =>
      right
      linarith
  cases h4 with
  | inl h5 =>
    have ha : c = -5 := by
      have h6 : a * b = -6 := h₀
      have h7 : a * b * c = 30 := h5
      have h8 : (-6) * c = 30 := by
        rw [show a * b = -6 by linarith] at h7
        linarith
      have h9 : c = -5 := by
        linarith
      exact h9
    have hb : a = 2 := by
      rw [ha] at h₁
      have h8 : a * (-5) = -10 := h₁
      have h9 : a = 2 := by
        linarith
      exact h9
    have hc : b = -3 := by
      rw [hb] at h₀
      have h8 : 2 * b = -6 := h₀
      have h9 : b = -3 := by
        linarith
      exact h9
    left
    exact ⟨h5, hb, hc, ha⟩
  | inr h5 =>
    have ha : c = 5 := by
      have h6 : a * b = -6 := h₀
      have h7 : a * b * c = -30 := h5
      have h8 : (-6) * c = -30 := by
        rw [show a * b = -6 by linarith] at h7
        linarith
      have h9 : c = 5 := by
        linarith
      exact h9
    have hb : a = -2 := by
      rw [ha] at h₁
      have h8 : a * 5 = -10 := h₁
      have h9 : a = -2 := by
        linarith
      exact h9
    have hc : b = 3 := by
      rw [hb] at h₀
      have h8 : -2 * b = -6 := h₀
      have h9 : b = 3 := by
        linarith
      exact h9
    right
    exact ⟨h5, hb, hc, ha⟩