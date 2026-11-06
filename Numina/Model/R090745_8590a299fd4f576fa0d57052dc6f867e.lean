import Mathlib

theorem algebra_2554 {a b : ℚ} (hab : b ≠ 0) (hab1 : a / b = 0) : ¬(a = 0 ∧ b = 0) := by 
  have h1 : a = 0 := by 
    field_simp [show b ≠ 0 by exact hab] at hab1 
    linarith 
  intro h 
  have h2 : b = 0 := h.right 
  contradiction