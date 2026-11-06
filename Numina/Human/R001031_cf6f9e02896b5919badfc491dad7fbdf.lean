import Mathlib

/- Benjamin is trying to break a combination lock. This particular type of lock has 5 digits from 0 to 9, and Benjamin just happens to know that there can be no repeated digits in the code for this type of lock. How many valid codes are there? -/
theorem algebra_19995 : ∏ i ∈ Finset.Ioc 5 10, i = 30240 := by
  exact rfl