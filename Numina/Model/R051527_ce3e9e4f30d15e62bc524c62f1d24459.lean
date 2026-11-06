import Mathlib
open Mathlib

theorem number_theory_2813 (n : ℕ) (h1 : n > 12) (h2 : n < 32)
(h3 : n % 2 = 1) (h4 : n % 3 = 2) (h5 : n % 4 = 3) : n = 23 := by
  interval_cases n <;> omega