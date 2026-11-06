import Mathlib

theorem number_of_factors_of_20_factorial : 
  (Nat.factorial 20).divisors.card = 41040 := by 
  rw [Nat.card_divisors]
  <;> native_decide