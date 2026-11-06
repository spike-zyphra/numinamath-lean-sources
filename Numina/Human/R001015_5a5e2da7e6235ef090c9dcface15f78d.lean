import Mathlib

/- In the prime factorization of $109!$, what is the exponent of $3$?  (Reminder: The number $n!$ is the product of the integers from 1 to $n$.  For example, $5!=5\cdot 4\cdot3\cdot2\cdot 1= 120$.) -/
theorem algebra_19871 : (Nat.factorization (Nat.factorial 109) 3) = 53 := by 
  native_decide
