import Mathlib

/- For each of the following sets of integers, express their greatest common divisor as a linear combination of these integers:
a) 6, 10, 15 -/
theorem number_theory_4538_1 : gcd (gcd 6 10) 15 = 1 := by rfl

/- For each of the following sets of integers, express their greatest common divisor as a linear combination of these integers:
b) 70, 98, 105 -/
theorem number_theory_4538_2 : gcd (gcd 70 98) 105 = 7 := by rfl

/- For each of the following sets of integers, express their greatest common divisor as a linear combination of these integers:
c) 280, 330, 405, 490 -/
theorem number_theory_4538_3 : gcd (gcd 280 330) (gcd 405 490) = 5 := by rfl
