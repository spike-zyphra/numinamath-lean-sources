import Mathlib

theorem algebra_169791 (x y : ℕ) :
    (y = 3 * x - 1 ∧ 6 * x * 4 * y = 1680) ↔ (x, y) = (5, 14) := by
  constructor
  · -- Forward implication: from the conditions, prove (x,y) = (5,14)
    intro ⟨h1, h2⟩
    have h3 : x = 5 := by
      have h5 : x ≤ 20 := by
        by_contra h
        push_neg at h
        have h6 : x ≥ 21 := by omega
        have h7 : y ≥ 62 := by
          omega
        nlinarith
      interval_cases x <;> omega
    have h4 : y = 14 := by
      omega
    simp [h3, h4]
  · -- Backward implication: (x,y) = (5,14) implies both conditions
    rintro ⟨rfl, rfl⟩
    constructor
    · -- $14 = 3 * 5 - 1$
      norm_num
    · -- $6 * 5 * 4 * 14 = 1680$
      norm_num