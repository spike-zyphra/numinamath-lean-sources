import Mathlib

/-
If $ a, b, $ and $ c $ are positive integers such that $ (a, b) = 1 $ (meaning $ a $ and $ b $ are coprime) and $ a $ divides the product $ b c $, then $ a $ must also divide $ c $.
-/
theorem number_theory_4553
    (a b c : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hcoprime : Int.gcd a b = 1)
    (hdiv : a ∣ b * c) :
    a ∣ c := by
  -- exact `Int.dvd_of_dvd_mul_right_of_gcd_one` in Mathlib
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hdiv hcoprime
