import Mathlib

/- The product of the base seven numbers $24_7$ and $30_7$ is expressed in base seven. What is the base seven sum of the digits of this product? -/
theorem number_theory_13058 : (Nat.digits 7 (Nat.ofDigits 7 [4, 2] * Nat.ofDigits 7 [0, 3])).sum = 6 := by
  native_decide
