import Mathlib

/- What is the product of the digits in the base 8 representation of $6543_{10}$? -/
theorem number_theory_12732 : (Nat.digits 8 6543).prod = 168 := by
  simp
  <;> rfl