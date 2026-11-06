import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_136706 {P Q : Set ℝ}
  (hP : P = {x | abs (x - 2) > 1}) (hQ : Q = {x | x^2 - 6 * x + 5 < 0}) :
  (Pᶜ ∪ Q) = {x | 1 ≤ x ∧ x < 5} := by
  ext x
  simp [hP, hQ]
  constructor
  · -- Assume x in Pᶜ ∪ Q
    intro h
    cases h with
    | inl h₁ =>
      constructor
      · -- Prove 1 ≤ x from |x - 2| ≤ 1
        linarith [abs_le.mp h₁]
      · -- Prove x < 5 from |x - 2| ≤ 1
        nlinarith [abs_le.mp h₁]
    | inr h₂ =>
      constructor
      · -- Prove 1 ≤ x from x^2 - 6*x + 5 < 0
        nlinarith
      · -- Prove x < 5 from x^2 - 6*x + 5 < 0
        nlinarith
  · -- Assume x in {x | 1 ≤ x ∧ x < 5}
    intro h
    rcases h with ⟨h₁, h₂⟩
    by_cases h₃ : abs (x - 2) ≤ 1
    · -- Case x in Pᶜ
      left
      simpa using h₃
    · -- Case x not in Pᶜ, need to show x in Q
      right
      cases abs_cases (x - 2) with
      | inl h₃ =>
        nlinarith
      | inr h₃ =>
        nlinarith