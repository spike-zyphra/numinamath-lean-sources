import Mathlib

theorem algebra_326357 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) :
    ∃ x y, (x = a ∧ y = b) ∨ (x = a ∧ y = c) ∨ (x = b ∧ y = c) ∧ x = -y := by
  refine' ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩