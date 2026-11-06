import Mathlib

theorem number_theory_96705 {x y : ℕ} (hx : x = 143) (hy : y = 195) :
(y - x) = 4 * gcd x y := by 
  subst x
  subst y
  norm_num [gcd]