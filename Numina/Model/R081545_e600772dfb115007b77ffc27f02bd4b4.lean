import Mathlib

theorem number_theory_264518 {x : ℕ} (hx : x % 3 = 1 ∧ x % 5 = 2) :
    x % 15 = 7 := by
  have h1 : x % 3 = 1 := hx.1
  have h2 : x % 5 = 2 := hx.2
  omega