import Mathlib

theorem number_theory_290533 (A B : ℕ) (hA : A < 10) (hB : B < 10)
    (h : A * 100 + A * 10 + A + A * 100 + A * 10 + B + A * 100 + B * 10 + B = 1503) :
    A^3 + B^2 = 57 := by
  interval_cases A <;> interval_cases B <;> omega