import Mathlib

theorem number_theory_6813 (x y : ℤ) : 111 * x - 321 * y = 75 ↔
    ∃ t : ℤ, x = -8 + 107 * t ∧ y = -3 + 37 * t := by 
  constructor
  · -- Assume 111 * x - 321 * y = 75, we need to prove ∃ t : ℤ, x = -8 + 107 * t ∧ y = -3 + 37 * t
    intro h 
    use (x + 8) / 107
    constructor
    · -- Show that x = -8 + 107 * t
      omega 
    · -- Show that y = -3 + 37 * t 
      omega 
  · -- Assume ∃ t : ℤ, x = -8 + 107 * t ∧ y = -3 + 37 * t, prove 111 * x - 321 * y = 75
    rintro ⟨t, hx, hy⟩
    rw [hx, hy]
    omega