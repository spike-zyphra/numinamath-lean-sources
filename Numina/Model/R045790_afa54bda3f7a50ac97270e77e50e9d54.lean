import Mathlib

theorem algebra_169838 {A B n : ℝ} (h : A ≠ 0) (h1 : (A * 1^(n + 1) + B * 1^n + 1) = 0)
    (h2 : (A * (n + 1) * 1^n + B * n * 1^(n - 1)) = 0) :
    A = n ∧ B = -(n + 1) := by
  have eq1 : A + B + 1 = 0 := by
    simp at h1
    linarith
  have eq2 : A * (n + 1) + B * n = 0 := by
    simp at h2
    linarith
  have eq3 : B = -1 - A := by
    linarith
  rw [eq3] at eq2
  have eq4 : A = n := by
    linarith
  have eq5 : B = -(n + 1) := by
    rw [eq4] at eq3
    linarith
  constructor
  · exact eq4
  · exact eq5