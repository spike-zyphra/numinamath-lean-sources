import Mathlib

theorem algebra_3771 (x : ℕ) (hx : x ≤ 38) :
    75 < 3 * x - 2 * (38 - x) ↔ x ≥ 31 := by 
  constructor
  · -- Forward direction: If score > 75, then x ≥ 31.
    intro h
    omega 
  · -- Backward direction: If x ≥ 31, then score > 75.
    intro h
    omega