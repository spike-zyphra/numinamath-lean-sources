import Mathlib
theorem number_theory_96211 : IsLeast {x | 0 < x ∧ ∃ (a b : ℤ), x = 300 * a + 210 * b} 30 := by
  constructor
  · -- First part: Show that 30 is in the set
    constructor
    · norm_num
    · -- Now, provide the existence of integers a and b such that 30 = 300*a + 210*b
      use -2, 3
      norm_num
  · -- Now, the second part: showing 30 is the smallest
    intro x ⟨hx, ⟨a, b, h⟩⟩
    have h1 : x = 300 * a + 210 * b := h
    omega