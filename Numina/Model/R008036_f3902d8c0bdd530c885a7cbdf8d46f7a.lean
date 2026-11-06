import Mathlib

theorem algebra_12666 : ∑ d in (60 : ℕ).divisors.filter Odd, d = 24 := by 
  native_decide