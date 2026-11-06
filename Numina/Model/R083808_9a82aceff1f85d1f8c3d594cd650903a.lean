import Mathlib

theorem algebra_6445 {A B C D : ℤ} (hAB : A * 3 = B * 2) (hBC : B * 1 = C * 5)
    (hCD : C * 2 = D * 7) (hsum : A + B + C + D = 2020) : D = 60 := by
  omega