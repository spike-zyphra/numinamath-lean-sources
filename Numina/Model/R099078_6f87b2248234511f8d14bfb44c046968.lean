import Mathlib

theorem algebra_322961 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : ∃! x, a * x ^ 2 + b * x + c = 0 ∧ b * x ^ 2 + c * x + a = 0 ∧
      c * x ^ 2 + a * x + b = 0) :
    a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) = 3 := by

  rcases h1 with ⟨x, ⟨h₁,h₂,h₃⟩, h⟩

  have h4 : a * x ^ 2 + b * x + c = 0 := h₁
  have h5 : b * x ^ 2 + c * x + a = 0 := h₂
  have h6 : c * x ^ 2 + a * x + b = 0 := h₃

  have eq_a : a = a * x ^ 3 := by
    have hc' : c = -a * x ^ 2 - b * x := by linarith
    rw [hc'] at h5
    nlinarith

  have hx3 : x ^ 3 = 1 := by
    have h7 : a = a * x ^ 3 := eq_a
    have : x ^ 3 = 1 := by
      apply (mul_left_inj' ha).mp
      linarith
    linarith

  have hx : x = 1 := by
    have h : x ^ 3 - 1 = 0 := by linarith [hx3]
    have factored : (x - 1) * (x ^ 2 + x + 1) = 0 := by
      ring_nf at h ⊢
      linarith
    cases' (mul_eq_zero.mp factored) with h7 h8
    · linarith
    · have h9 : x ^ 2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1/2)]
      linarith

  rw [hx] at h₁ h₂ h₃

  have h7 : a + b + c = 0 := by
    nlinarith

  have h8 : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  
  have h9 : a^3 + b^3 + c^3 = 3 * a * b * c := by
    have fact : a + b + c = 0 := h7
    have h9 : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by nlinarith
  
    rw [fact] at h9
    have h10 : a^3 + b^3 + c^3 - 3 * a * b * c = 0 := by
      linarith
  
    linarith
  
  have eq1 : a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) = (a^3 + b^3 + c^3) / (a * b * c) := by
    field_simp [h8]
    ring
  
  rw [eq1]
  have h11 : a^3 + b^3 + c^3 = 3 * (a * b * c) := by
    linarith [h9]

  have h12 : (a^3 + b^3 + c^3) / (a * b * c) = 3 := by
    have h11' : a^3 + b^3 + c^3 = 3 * (a * b * c) := by linarith
    rw [h11']
    field_simp [h8]
    <;> nlinarith

  linarith