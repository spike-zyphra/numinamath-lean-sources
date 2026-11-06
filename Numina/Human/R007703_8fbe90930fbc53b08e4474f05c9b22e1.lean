import Mathlib

/- Find the greatest common divisor (GCD) of each of the following pairs of integers:
a) 15 and 35
b) 0 and 111
c) -12 and 18
d) 99 and 100
e) 11 and 121
f) 100 and 102-/
theorem number_theory_4506 :
    Int.gcd 15 35 = 5 ∧
    Int.gcd 0 111 = 111 ∧
    Int.gcd (-12) 18 = 6 ∧
    Int.gcd 99 100 = 1 ∧
    Int.gcd 11 121 = 11 ∧
    Int.gcd 100 102 = 2 := by
  -- verify by computation
  split_ands <;> norm_num
