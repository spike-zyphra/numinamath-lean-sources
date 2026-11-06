import Mathlib

noncomputable def F_9328 : Polynomial ℝ :=
 2 * Polynomial.X^2 + 3 * Polynomial.X + (-4)

theorem algebra_9328 {a : ℝ} (h : Polynomial.eval a F_9328 = 0) :
 2 * a^2 + 3 * a = 4 := by
  simp [F_9328] at h
  linarith