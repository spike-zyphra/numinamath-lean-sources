import Mathlib

theorem algebra_180884 (f : ℝ × ℝ → ℝ) (h : ∀ A B C, f ((A.1 + B.1 + C.1) / 3, (A.2 + B.2 + C.2) / 3) = f A + f B + f C) :
    ∀ A, f A = 0 := by
  intro A
  have h1 := h A A A
  have eq1 : ((A.1 + A.1 + A.1) / 3 : ℝ) = A.1 := by ring
  have eq2 : ((A.2 + A.2 + A.2) / 3 : ℝ) = A.2 := by ring
  rw [eq1, eq2] at h1
  simp at h1 ⊢
  linarith