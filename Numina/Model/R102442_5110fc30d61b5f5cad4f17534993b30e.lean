import Mathlib

theorem number_theory_2794 {A : ℕ} (hA1 : A % 3 = 2) (hA2 : A % 4 = 1) :
    A % 12 = 5 := by
  have h1 : A % 3 = 2 := hA1
  have h2 : A % 4 = 1 := hA2
  omega