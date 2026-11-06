import Mathlib

theorem algebra_185632 (n : ℕ) (hn : n ≤ 25) :
    4 * n - (25 - n) ≥ 60 ↔ n ≥ 17 := by 
  constructor
  · -- Forward direction: If 4n - (25 - n) ≥ 60, then n ≥ 17
    intro h
    omega
  · -- Backward direction: If n ≥ 17, then 4n - (25 - n) ≥ 60
    intro h
    omega