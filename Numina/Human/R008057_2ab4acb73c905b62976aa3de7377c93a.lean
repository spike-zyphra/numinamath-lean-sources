import Mathlib

/- What is the remainder when the base 4 number $120301232_4$ is divided by 8? Express your answer in base 10. -/
theorem number_theory_22922 : (Nat.ofDigits 4 [2, 3, 2, 1, 0, 3, 0, 2, 1]) % 8 = 6 := by 
  rfl