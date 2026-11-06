import Mathlib
open Real
theorem algebra_95958 (a b c : ℕ) (ha : a = 70) (hb : b = 80) (hc : c = 90)
(h : a * 10 + b * 20 + c * 30 = 60 * x) :
x = 83 := by
  subst ha
  subst hb
  subst hc
  omega