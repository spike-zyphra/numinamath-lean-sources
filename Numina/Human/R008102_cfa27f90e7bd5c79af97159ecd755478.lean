import Mathlib

/- The $\$4.55$ in Carol's piggy bank consists of quarters and nickels. There are seven more nickels than quarters. How many nickels does Carol have in her bank? -/
theorem algebra_15068 (q n : ℕ) (h : n = q + 7) (h' : 25*q+5*n=455) :
    n=21 := by
  subst h
  linarith