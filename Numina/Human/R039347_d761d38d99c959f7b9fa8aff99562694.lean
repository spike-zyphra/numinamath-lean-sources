import Mathlib

/- A suitcase lock has 4 dials with the digits $0, 1, 2,..., 9$ on each. How many different settings are possible if all four digits have to be different? -/
theorem algebra_21626 : (Nat.factorial 10) / (Nat.factorial (10 - 4)) = 5040 := by
  exact rfl