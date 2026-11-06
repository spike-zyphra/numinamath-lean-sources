import Mathlib

theorem algebra_274125 (x y : ℕ) (hxy : x > 0 ∧ y > 0)
    (h : x * 2 ≤ y * 3) (h' : x * 3 + y * 2 = 994) (h'' : x * 4 + y * 3 = 1120) :
    x = 25 ∧ y = 30 := by 
  -- Lean will detect inconsistency, since the system of equations is contradictory.
  omega