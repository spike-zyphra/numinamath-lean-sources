import Mathlib

theorem algebra_2097
    (a : ℝ)
    (A : ℝ × ℝ)
    (hA : A = (a - 2, a - 1)) :
    ¬(A.1 > 0 ∧ A.2 < 0) := by
  intro h
  rw [hA] at h
  simp at h
  linarith