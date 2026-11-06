import Mathlib

theorem number_theory_235588 (x : ℕ) (h : x ≠ 0) (h1 : 25 * x = 1) :
    3 / x = 75 := by
  have h2 : x = 0 := by
    omega
  contradiction