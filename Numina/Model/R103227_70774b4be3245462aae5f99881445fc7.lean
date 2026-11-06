import Mathlib

theorem inequalities_72708 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a^2 + b^2 + c^2 + d^2 = 4) :
    ∃ x y, (x = a ∧ y = b) ∨ (x = a ∧ y = c) ∨ (x = a ∧ y = d) ∨
    (x = b ∧ y = c) ∨ (x = b ∧ y = d) ∨ (x = c ∧ y = d) ∧ x + y ≤ 2 := by

  refine ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩