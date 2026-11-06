import Mathlib

theorem algebra_178293 {a b c : ℝ} (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a = (b + c) / 2) (h₂ : b = (a + c) / 5) :
    c / (a + b) = 1 := by
  have h3 : 2 * a = b + c := by
    linarith
  have h4 : 5 * b = a + c := by
    linarith
  have h5 : a = 2 * b := by
    linarith
  have h6 : c = 3 * b := by
    rw [show a = 2 * b by linarith] at h4
    linarith
  have h7 : 0 < a := h₀.1
  have h8 : 0 < b := h₀.2.1
  have h9 : 0 < c := h₀.2.2
  have h11 : a + b = 3 * b := by
    rw [show a = 2 * b by linarith]
    linarith
  rw [show c = 3 * b by linarith, show a + b = 3 * b by linarith]
  have hb1 : b ≠ 0 := by linarith [h₀.2.1]
  field_simp [hb1]
  <;> ring_nf <;> linarith