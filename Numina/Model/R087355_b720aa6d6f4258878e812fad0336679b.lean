import Mathlib

theorem algebra_6391 {f : ℝ × ℝ → ℝ} (h : ∀ A B C : ℝ × ℝ, f ((A.1 + B.1 + C.1) / 3, (A.2 + B.2 + C.2) / 3) = f A + f B + f C) :
    ∀ A : ℝ × ℝ, f A = 0 := by 
  intro A
  have h1 := h A A A
  simp [show A.1 + A.1 + A.1 = 3 * A.1 by ring, show A.2 + A.2 + A.2 = 3 * A.2 by ring] at h1
  linarith