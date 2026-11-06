import Mathlib

theorem algebra_95778 {P : ℕ} (hP : P = 226504825) {A : ℕ} (hA : A = 3615122)
    {h : (5280 ^ 2) * A = x * P} :
    x = 500000 := by
  subst hP
  subst hA
  omega