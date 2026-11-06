import Mathlib

theorem number_theory_285330 (k : ℤ) : Odd (2007 + 2 * k^2) := by
  use 1003 + k^2
  ring