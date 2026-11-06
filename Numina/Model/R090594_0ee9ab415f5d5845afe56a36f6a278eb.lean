import Mathlib

theorem number_theory_12873 (A B : ℕ) (hA : A < 10) (hB : B < 10)
    (h : (B * 100 + B * 10 + A) + (4 * 100 + 1 * 10 + B) = A * 100 + 1 * 10 + 5 * 6 + 2) :
    A - B = 1 := by
  omega