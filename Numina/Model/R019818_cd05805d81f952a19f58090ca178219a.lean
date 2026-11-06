import Mathlib

theorem number_theory_6718 {x y : ℤ} (h : 205*x+93*y=1) :
    ∃ t : ℤ, x=-44+93*t ∧ y=97-205*t := by 
  use (x + 44) / 93
  constructor
  · -- Show x = -44 + 93t
    omega
  · -- Show y = 97 - 205t
    omega