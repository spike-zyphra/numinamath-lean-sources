import Mathlib

/- What is the greatest common factor of $20 !$ and $200,\!000$?  (Reminder: If $n$ is a positive integer, then $n!$ stands for the product $1\cdot 2\cdot 3\cdot \cdots \cdot (n-1)\cdot n$.) -/
theorem number_theory_23161 : Nat.gcd (Nat.factorial 20) 200000 = 40000 := by 
  rfl