import Mathlib

theorem algebra_142270 {a b : ℝ} (ha : a > 0) (hb : b > 0)
    (h1 : (a + b) / 2 = 2) (h2 : 2 * a * b / (a + b) = 2) :
    a = 2 ∧ b = 2 := by
  have h1' : a + b = 4 := by
    linarith
  have h3 : 2 * a * b / (a + b) = 2 := h2
  rw [h1'] at h3
  have h4 : 2 * a * b / 4 = 2 := by
    exact h3
  have h5 : a * b = 4 := by
    field_simp at h4 ⊢
    nlinarith
  have h6 : a = 2 := by
    have h7 : b = 4 - a := by linarith
    rw [h7] at h5
    have h8 : (a - 2) ^ 2 = 0 := by
      nlinarith
    have ha2 : a - 2 = 0 := by
      rw [sq_eq_zero_iff] at h8
      exact h8
    linarith
  have h7 : b = 2 := by
    nlinarith
  exact ⟨h6, h7⟩