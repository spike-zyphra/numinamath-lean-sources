import Mathlib

theorem number_theory_5143 (x : ZMod 15) (hx : x^2 = 1) : x = 1 ∨ x = 4 ∨ x = 11 ∨ x = 14 := by 
  have h1 : x^2 = 1 := hx
  fin_cases x <;> simp [pow_two] at h1 ⊢ <;> tauto