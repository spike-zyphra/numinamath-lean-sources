import Mathlib

/- a) Show that if $ p $ is a prime number and $ a $ is a positive integer such that $ p $ divides $ a^2 $, then $ p $ also divides $ a $.-/
theorem number_theory_4596_1
    (p : ℤ)
    (a : ℤ)
    (ppos : p > 0)
    (pprime : Prime p)
    (apos : a > 0)
    (pasq : p ∣ a^2) :
    p ∣ a :=
  -- exact `Prime.dvd_of_dvd_pow` in Mathlib
  Prime.dvd_of_dvd_pow pprime pasq

/- b) Show that if $ p $ is a prime number, $ a $ is an integer, and $ n $ is a positive integer such that $ p $ divides $ a^n $, then $ p $ also divides $ a $.-/
theorem number_theory_4596_2
    (p : ℤ)
    (a : ℤ)
    (n : ℕ)
    (ppos : p > 0)
    (pprime : Prime p)
    (npos : n > 0)
    (pan : p ∣ a^n) :
    p ∣ a :=
  -- exact `Prime.dvd_of_dvd_pow` in Mathlib
  Prime.dvd_of_dvd_pow pprime pan
