import Mathlib

theorem algebra_320426 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a^3 + b^3 + c^3 = 0) :
    a^15 + b^15 + c^15 = 0 := by
  have h2 : a * b * c = 0 := by
    have h_id : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - (a*b + a*c + b*c)) := by 
      ring
    rw [h₀] at h_id
    linarith [h₁, h_id]
  cases' (mul_eq_zero.mp h2) with h6 h7
  cases' (mul_eq_zero.mp h6) with h3 h4
  · -- Case a = 0
    have h5 : a = 0 := h3
    have h6 : c = -b := by
      linarith [h₀, h5]
    rw [h5, show c = -b by linarith [h₀, h5]]
    ring_nf
  · -- Case b = 0
    have h5 : b = 0 := h4
    have h6 : c = -a := by
      linarith [h₀, h5]
    rw [h5, show c = -a by linarith [h₀, h5]]
    ring_nf
  · -- Case c = 0
    have h5 : c = 0 := h7
    have h8 : b = -a := by
      linarith [h₀, h5]
    rw [h5, show b = -a by linarith [h₀, h5]]
    ring_nf