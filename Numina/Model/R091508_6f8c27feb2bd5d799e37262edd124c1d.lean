import Mathlib

theorem algebra_6261
    (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a / b = 1 / 3)
    (h₂ : b / c = 3 / 5)
    (h₃ : a * b * c = 1875) :
    a = 5 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have h4 : 3 * a = b := by
    have h5 : b ≠ 0 := by linarith
    field_simp at h₁
    linarith
  have h6 : 5 * b = 3 * c := by
    have h7 : c ≠ 0 := by linarith
    field_simp at h₂
    linarith
  have h7 : c = 5 * a := by
    have h9 : b = 3 * a := by linarith
    rw [h9] at h6
    nlinarith
  have h8 : a * (3 * a) * (5 * a) = 1875 := by
    have h9 : b = 3 * a := by linarith
    have h10 : c = 5 * a := h7
    rw [h9, h10] at h₃
    nlinarith
  have h9 : 15 * a^3 = 1875 := by
    ring_nf at h8 ⊢
    nlinarith
  have h10 : a^3 = 125 := by 
    nlinarith
  have h11 : a = 5 := by
    have h12 : a^3 - 125 = 0 := by
      nlinarith
    have h13 : (a - 5) * (a^2 + 5 * a + 25) = 0 := by
      ring_nf at h12 ⊢
      <;> nlinarith
    cases' (mul_eq_zero.mp h13) with h14 h15
    · linarith
    · -- Show that the quadratic has no real roots
      nlinarith [sq_nonneg (a + 5 / 2)]
  exact h11