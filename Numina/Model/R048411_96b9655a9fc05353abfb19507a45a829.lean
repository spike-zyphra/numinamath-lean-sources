import Mathlib

theorem number_theory_261 (x y : ℤ) :
    17 * x + 11 * y = 1 ↔ ∃ t, x = 2 + 11 * t ∧ y = -3 - 17 * t := by
  constructor
  · -- Forward direction: if (x, y) satisfies the equation, then there exists t
    intro h
    use (x - 2) / 11
    constructor
    · -- Show x = 2 + 11 * t
      omega
    · -- Show y = -3 - 17 * t
      omega
  · -- Backward direction: if there exists t
    rintro ⟨t, hx, hy⟩
    rw [hx, hy]
    linarith