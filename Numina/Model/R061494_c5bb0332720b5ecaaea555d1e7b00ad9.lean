import Mathlib

theorem number_theory_318064 (x y : ℤ) : 41*x+177*y=4 ↔ ∃ t : ℤ, x=-328+177*t ∧ y=76-41*t := by
  constructor
  · -- Assume 41 * x + 177 * y = 4 prove ∃ t : ℤ, x=-328+177*t ∧ y=76-41*t
    intro h
    use (x + 328) / 177
    constructor
    · -- Show x = -328 + 177t
      omega
    · -- Show y = 76 - 41t
      omega
  · -- Assume ∃ t : ℤ, x=-328+177*t ∧ y=76-41*t prove 41*x+177*y=4
    rintro ⟨t, hx, hy⟩
    rw [hx, hy]
    linarith