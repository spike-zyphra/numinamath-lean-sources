import Mathlib

open Real

theorem inequalities_186094 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ x y, x = a ∧ y = b ∨ x = b ∧ y = a ∨ x = a ∧ y = c ∨ x = c ∧ y = a ∨
    x = b ∧ y = c ∨ x = c ∧ y = b ∨ x = a ∧ y = c ∨ x = c ∧ y = a ∧ 0 ≤ (x - y) / (1 + x * y) ∧
    (x - y) / (1 + x * y) ≤ 1 := by
  refine' ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩