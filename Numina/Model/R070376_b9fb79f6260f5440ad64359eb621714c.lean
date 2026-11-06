import Mathlib

theorem algebra_8179 (x y : ℕ) (h : x + y = 10) (h' : 12*x+10*y≤105) :
    (x=0 ∧ y=10) ∨ (x=1 ∧ y=9) ∨ (x=2 ∧ y=8) := by 
  omega