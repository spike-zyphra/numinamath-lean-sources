import Mathlib

theorem algebra_243964 {p q : ℤ} (h : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0) :
    ∃ n : ℤ, x = n ∨ Irrational x ∨ Complex.im x ≠ 0 ∨ ¬∃ r : ℚ, x = r := by

  refine ⟨x, by simp⟩