import Mathlib

theorem calculus_15706 (k : ℝ) :
    (∀ A B C D : ℝ × ℝ × ℝ,
      (3 * (A.1 - 0) - 2 * (B.1 - 0) + 5 * (C.1 - 0) + k * (D.1 - 0) = 0 ∧
       3 * (A.2.1 - 0) - 2 * (B.2.1 - 0) + 5 * (C.2.1 - 0) + k * (D.2.1 - 0) = 0 ∧
       3 * (A.2.2 - 0) - 2 * (B.2.2 - 0) + 5 * (C.2.2 - 0) + k * (D.2.2 - 0) = 0)) →
    k = -6 := by
  intro h
  have eq1 := h (1, 0, 0) (0, 1, 0) (0, 0, 1) (1, 1, 1)
  simp at eq1
  have eq2 := h (1, 2, 3) (2, 3, 4) (3, 4, 5) (4, 5, 6)
  simp at eq2
  linarith