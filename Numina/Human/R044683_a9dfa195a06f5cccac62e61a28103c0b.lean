import Mathlib

open Real

/- In a 3-dimensional coordinate system with $x$-, $y$-, and $z$-axes, $P$ is a point on the line $y = -x + 1$ in the $xy$-plane and $Q$ is a point on the line $z = -2x + 1$ in the $xz$-plane.  Compute the smallest possible value for $PQ.$-/
theorem calculus_18606 :
  IsLeast {d | ∃ P Q : EuclideanSpace ℝ (Fin 3), d = dist P Q ∧ P 1 = -P 0 + 1 ∧ P 2 = 0 ∧ Q 2 = -2 * Q 0 + 1 ∧ Q 1 = 0} (1 / 3) := by
  constructor
  · -- $1 / 3$ is a possible value
    use ![7 / 9, 2 / 9, 0]
    use ![5 / 9, 0, -1 / 9]
    simp only [one_div, EuclideanSpace.dist_eq, Nat.succ_eq_add_one, Nat.reduceAdd, dist_eq, sq_abs, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_zero, Matrix.cons_val_two, Matrix.tail_cons, zero_sub, even_two, Even.neg_pow, neg_mul, and_true, true_and]
    have sqrteq : √9 = 3 := by
      refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
      any_goals
      norm_num
    norm_num [sqrteq]
  -- $1 / 3$ is the least such value
  intro d din
  rcases din with ⟨P, Q, hd, hP1, hP2, hQ1, hQ2⟩
  simp only [EuclideanSpace.dist_eq, dist_eq, sq_abs, Fin.sum_univ_three, Fin.isValue, hP1, hQ2, sub_zero, hP2, hQ1, neg_mul, zero_sub, neg_add_rev, neg_neg] at hd
  have le : (1 / 3) ^ 2 ≤ (P 0 - Q 0) ^ 2 + (-P 0 + 1) ^ 2 + (-1 + 2 * Q 0) ^ 2 := by
    have eq : (P 0 - Q 0) ^ 2 + (-P 0 + 1) ^ 2 + (-1 + 2 * Q 0) ^ 2 = (2 * P 0 - Q 0 - 1) ^ 2 / 2 + (9 * (Q 0 - 5 / 9) ^ 2 + 2 / 9) / 2 := by
      ring
    rw [eq]
    nlinarith
  rw [hd]
  exact Real.le_sqrt_of_sq_le le