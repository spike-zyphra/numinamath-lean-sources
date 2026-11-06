import Mathlib

theorem algebra_151595 (x : ZMod 12) (hx : x^2 + 3 * x + 2 = 0) :
    x = 2 ∨ x = -5 ∨ x = -2 ∨ x = -1 := by 
  have h1 : x^2 + 3 * x + 2 = 0 := hx
  fin_cases x <;> simp [pow_two] at h1 ⊢ <;> tauto