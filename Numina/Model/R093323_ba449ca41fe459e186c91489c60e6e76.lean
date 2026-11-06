import Mathlib

theorem other_314534 {P A : ℕ} (hP : P = 226504825) (hA : A = 3615122)
    (h : A * 5280^2 = x * P) :
    x = 500000 := by 
  subst P
  subst A
  omega