import Mathlib

theorem number_theory_79451 (x y : ℤ) (h : 41 ∣ 25*x+31*y ∨ 41 ∣ 3*x+7*y) :
    41 ∣ 25*x+31*y ∧ 41 ∣ 3*x+7*y := by
  cases h with
  | inl h1 =>
    have h2 : 41 ∣ 3 * x + 7 * y := by
      omega
    constructor
    · exact h1
    · exact h2
  | inr h2 =>
    have h1 : 41 ∣ 25 * x + 31 * y := by
      omega
    constructor
    · exact h1
    · exact h2