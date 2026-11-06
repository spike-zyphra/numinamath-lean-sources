import Mathlib

theorem algebra_9224 (x : ℝ) :
    (x > -6 - 2 * x ∧ x ≤ (3 + x) / 4) ↔ (-2 < x ∧ x ≤ 1) := by 
  constructor
  · -- Assume (x > -6 - 2 * x ∧ x ≤ (3 + x) / 4), prove (-2 < x ∧ x ≤ 1)
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Derive x > -2 from x > -6 - 2 * x
      linarith
    · -- Derive x ≤ 1 from x ≤ (3 + x) / 4
      linarith
  · -- Assume (-2 < x ∧ x ≤ 1), prove (x > -6 - 2 * x ∧ x ≤ (3 + x) / 4)
    rintro ⟨hx1, hx2⟩
    constructor
    · -- Derive x > -6 - 2 * x from x > -2
      linarith
    · -- Derive x ≤ (3 + x) / 4 from x ≤ 1
      linarith