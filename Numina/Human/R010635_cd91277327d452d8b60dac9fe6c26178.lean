import Mathlib

/-The integers greater than -2 and not greater than 3 are.-/
theorem algebra_9074 : {x : ℤ | -2 < x ∧ x ≤ 3} = {-1, 0, 1, 2, 3} := by 
  have : Finset.Ioc (-2 : ℤ) 3 = {-1, 0, 1, 2, 3} := rfl
  simpa using congr(($(this) : Set ℤ))
