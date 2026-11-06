import Mathlib

/- Find the greatest common divisor (GCD) of each of the following sets of integers:
a) 8, 10, 12
b) 5, 25, 75
c) 99, 9999, 0
d) 6, 15, 21
e) -7, 28, -35
f) 0, 0, 1001.-/
theorem number_theory_4521 :
    let gcd3 (a b c : ℤ) : ℤ := a.gcd (b.gcd c)
    gcd3 8 10 12 = 2 ∧
    gcd3 5 25 75 = 5 ∧
    gcd3 99 9999 0 = 99 ∧
    gcd3 6 15 21 = 3 ∧
    gcd3 (-7) 28 (-35) = 7 ∧
    gcd3 0 0 1001 = 1001 := by
  -- verify by computation
  native_decide
