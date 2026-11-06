import Mathlib

theorem algebra_1555 (a b : ℚ) (h₀ : a ≠ b) (h₁ : 0 = (a + b) / 2) :
    1995 * a * (26 / (3 * b)) = -17290 := by
  have h2 : a + b = 0 := by
    linarith
  have h3 : b = -a := by linarith
  have h4 : b ≠ 0 := by
    intro h
    have ha : a = 0 := by linarith [h3, h]
    have hb : b = 0 := by linarith [h]
    have h5 : a = b := by
      linarith
    contradiction
  have h5 : a ≠ 0 := by
    intro h
    have hb : b = 0 := by linarith [h3, h]
    have h5 : a = b := by
      linarith
    contradiction
  rw [show b = -a by linarith [h3]]
  field_simp [show -a ≠ 0 by intro h; apply h5; linarith, h5, h₀]
  <;> nlinarith