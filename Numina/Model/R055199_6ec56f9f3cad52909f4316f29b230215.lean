import Mathlib

theorem number_theory_197165 (x y : ℕ) :
    3 * x + 7 * y = 23 ↔ (x = 3 ∧ y = 2) := by
  constructor
  · -- Assume 3 * x + 7 * y = 23, prove x = 3 ∧ y = 2
    intro h
    have h1 : 3 * x + 7 * y = 23 := h
    have h2 : x ≤ 7 := by
      omega
    have h3 : y ≤ 3 := by
      omega
    have h4 : x = 3 := by
      omega
    have h5 : y = 2 := by
      omega
    exact ⟨h4, h5⟩
  · -- Assume x = 3 ∧ y = 2, prove 3 * x + 7 * y = 23
    rintro ⟨rfl, rfl⟩
    all_goals
      omega