import Mathlib

theorem algebra_30341 {a b c d : ℝ}
    (h₀ : a * b + c * d = 6) (h₁ : a * c + b * d = 3) (h₂ : a * d + b * c = 2)
    (h₃ : a + b + c + d = 6) :
    (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 0 ∧ d = 1) ∨
    (a = 1 ∧ b = 0 ∧ c = 3 ∧ d = 2) ∨ (a = 3 ∧ b = 2 ∧ c = 1 ∧ d = 0) := by

  have h4 : (a + d) * (b + c) = 9 := by
    nlinarith
  have h5 : (a + c) * (b + d) = 8 := by
    nlinarith
  have h6 : a + d = 3 := by
    have h7 : a + d + (b + c) = 6 := by linarith
    have h8 : (a + d) * (b + c) = 9 := h4
    have h9 : (a + d - 3) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (a + d - 3), sq_nonneg (b + c - 3)]
    have h10 : a + d - 3 = 0 := by 
      nlinarith
    linarith
  have h7 : b + c = 3 := by
    nlinarith
  have h8 : d = 3 - a := by linarith
  have h9 : c = 3 - b := by linarith
  have h10 : a * b + (3 - b) * (3 - a) = 6 := by 
    rw [show d = 3 - a by linarith, show c = 3 - b by linarith] at h₀
    linarith
  have h11 : a * (3 - a) + b * (3 - b) = 2 := by 
    rw [show d = 3 - a by linarith, show c = 3 - b by linarith] at h₂
    linarith
  have h12 : (a + b) ^ 2 - 6 * (a + b) + 5 = 0 := by
    nlinarith [sq_nonneg (a - b)]
  have h13 : (a + b - 5) * (a + b - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h13) with h14 h15
  · -- When a + b = 5.
    have h16 : a + b = 5 := by linarith
    have h17 : a * b = 6 := by
      nlinarith
    have h18 : (a - 2) * (a - 3) = 0 := by
      nlinarith [sq_nonneg (a - b)]
    cases' (mul_eq_zero.mp h18) with h19 h20
    ·
      have ha1 : a = 2 := by linarith
      have hb1 : b = 3 := by linarith
      have hc1 : c = 0 := by linarith
      have hd1 : d = 1 := by linarith
      right
      left
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    ·
      have ha1 : a = 3 := by linarith
      have hb1 : b = 2 := by linarith
      have hc1 : c = 1 := by linarith
      have hd1 : d = 0 := by linarith
      right
      right
      right
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · -- When a + b = 1.
    have h21 : a + b = 1 := by linarith
    have h17 : a * b = 0 := by
      nlinarith
    have h23 : a * b = 0 := h17
    cases' (mul_eq_zero.mp h23) with h24 h25
    ·
      have ha1 : a = 0 := by linarith
      have hb1 : b = 1 := by linarith
      have hc1 : c = 2 := by linarith
      have hd1 : d = 3 := by linarith
      left
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    ·
      have ha1 : a = 1 := by linarith
      have hb1 : b = 0 := by linarith
      have hc1 : c = 3 := by linarith
      have hd1 : d = 2 := by linarith
      right
      right
      left
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩