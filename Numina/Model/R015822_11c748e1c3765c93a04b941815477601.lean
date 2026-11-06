import Mathlib

theorem number_theory_109155 (x y : ℕ) (hx : x * 12 + y * 6 ≥ 70) (hy : x * 12 + y * 6 ≤ 80) :
    x * 12 + y * 6 = 72 ∨ x * 12 + y * 6 = 78 := by
  omega