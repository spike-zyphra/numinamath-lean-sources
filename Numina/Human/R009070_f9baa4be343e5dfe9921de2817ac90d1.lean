import Mathlib

/- Find all values of $x$ that satisfy the equation $|x-3|=2x+4$. Express your answers in simplest fractional form. -/
theorem algebra_13099 (x : ℚ) : abs (x - 3) = 2 * x + 4 ↔ x = -1 / 3 := by 
  rw [abs_eq_max_neg]
  constructor
  intro h
  cases' max_eq_iff.mp h with h₁ h₂
  linarith
  linarith
  intro h
  rw [h]
  norm_num