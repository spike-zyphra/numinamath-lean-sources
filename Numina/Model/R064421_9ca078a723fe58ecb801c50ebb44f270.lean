import Mathlib

open Real
open scoped BigOperators

theorem inequalities_597967 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  ∃ x y, x = a ∧ y = b ∨ x = b ∧ y = a ∨ x = a ∧ y = c ∨ x = b ∧ y = c ∨
  x = c ∧ y = a ∨ x = c ∧ y = b ∧ (x / y < (Real.sqrt 5 + 1) / 2 ∧ (Real.sqrt 5 - 1) / 2 < x / y) := by
    refine' ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩