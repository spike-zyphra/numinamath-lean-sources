import Mathlib

theorem algebra_97646 (k l : ℕ) (hk : k = 30) (hl : l = 10)
(h : l + 6 * t = 2 * (k + 2 * t)) :
t = 25 := by
  subst hk
  subst hl
  omega