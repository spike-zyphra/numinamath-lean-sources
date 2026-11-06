import Mathlib


/- Use the Euclidean algorithm to find the greatest common divisors (GCD) of the following pairs of numbers:
a) (45, 75) -/
theorem number_theory_4536_1 : gcd 45 75 = 15 := by
  calc gcd 45 75
    _ = gcd 45 30 := by rfl
    _ = gcd 30 15 := by rfl
    _ = gcd 15 0 := by rfl
    _ = 15 := by rfl

/- Use the Euclidean algorithm to find the greatest common divisors (GCD) of the following pairs of numbers:
b) (102, 222) -/
theorem number_theory_4536_2 : gcd 102 222 = 6 := by rfl

/- Use the Euclidean algorithm to find the greatest common divisors (GCD) of the following pairs of numbers:
c) (666, 1414) -/
theorem number_theory_4536_3 : gcd 666 1414 = 2 := by rfl

/- Use the Euclidean algorithm to find the greatest common divisors (GCD) of the following pairs of numbers:
d) (20785, 44350) -/
theorem number_theory_4536_4 : gcd 20785 44350 = 5 := by rfl
