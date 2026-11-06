import Mathlib

theorem number_theory_11006 : IsLeast {x | 0 < x ∧ x % 4 = 3 ∧ x % 5 = 4 ∧ x % 6 = 5} 59 := by
  constructor
  · -- Show that 59 is in the set
    show 0 < (59 : ℕ) ∧ (59 : ℕ) % 4 = 3 ∧ (59 : ℕ) % 5 = 4 ∧ (59 : ℕ) % 6 = 5
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 59 is the smallest
    intro x hx
    rcases hx with ⟨h_pos, h1, h2, h3⟩
    omega