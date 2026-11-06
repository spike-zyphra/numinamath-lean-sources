import Mathlib

theorem number_theory_321806 : {(x, y) : ℤ × ℤ | 205 * x + 93 * y = 7} =
    {(x, y) | ∃ t : ℤ, x = -308 - 93 * t ∧ y = 679 + 205 * t} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfies 205 * x + 93 * y = 7; prove there exists t such that x = -308 - 93 * t and y = 679 + 205 * t
    intro h
    use ((-x - 308) / 93)
    constructor
    · -- Show x = -308 - 93 * t
      omega
    · -- Show y = 679 + 205 * t
      omega
  · -- Assume there exists t such that x = -308 - 93 * t and y = 679 + 205 * t; prove 205 * x + 93 * y = 7
    rintro ⟨t, hx, hy⟩
    rw [hx, hy]
    linarith