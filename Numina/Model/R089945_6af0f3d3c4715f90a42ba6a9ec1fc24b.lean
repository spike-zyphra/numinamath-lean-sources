import Mathlib

theorem number_theory_222725 {n : ℤ} (hn : n % 3 = 2 ∧ n % 4 = 1) :
    n % 12 = 5 := by
  rcases hn with ⟨h1, h2⟩
  omega