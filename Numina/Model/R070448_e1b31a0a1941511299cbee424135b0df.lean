import Mathlib

theorem inequalities_89699 (a b c d e : ℝ) (h₀ : |a| ≤ 1) (h₁ : |b| ≤ 1)
    (h₂ : |c| ≤ 1) (h₃ : |d| ≤ 1) (h₄ : |e| ≤ 1) (h₅ : a + b + c + d + e = 1) :
    ∃ x y z, x = a ∧ y = b ∧ z = c ∨ x = b ∧ y = c ∧ z = d ∨ x = c ∧ y = d ∧ z = e ∨
    x = d ∧ y = e ∧ z = a ∨ x = e ∧ y = a ∧ z = b ∧
    x + y ≥ 0 ∧ y + z ≥ 0 ∧ x + y + z ≥ 0 := by
  use a, b, c
  left
  constructor
  · rfl
  constructor
  · rfl
  · rfl