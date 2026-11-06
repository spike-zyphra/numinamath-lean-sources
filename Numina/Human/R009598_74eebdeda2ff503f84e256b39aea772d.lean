import Mathlib

noncomputable def F_9328 : Polynomial ℝ :=
 2 * Polynomial.X^2 + 3 * Polynomial.X + (-4)

/-Find the standard equation of the parabola that passes through the point $P(4,-2)$.-/
theorem algebra_9328 {a : ℝ} (h : Polynomial.eval a F_9328 = 0) :
 2 * a^2 + 3 * a = 4 := by
  have root_value_equality (h : 2 * a^2 + 3 * a - 4 = 0) :
      2 * a^2 + 3 * a = 4 := by
    have h1 := eq_add_of_sub_eq h
    ring_nf
    rw[add_comm,mul_comm,zero_add] at h1
    nth_rw 2 [mul_comm]
    exact h1
  have root_evaluation {a : ℝ} (h : Polynomial.eval a F_9328 = 0) :
      2 * a^2 + 3 * a - 4 = 0 := by
    simp[F_9328] at h
    exact h
  exact root_value_equality (root_evaluation h)
