import Mathlib

open Real Set

/- Let $a,$ $b,$ $c$ be nonzero real numbers.  Find the maximum angle between the vectors $\begin{pmatrix} a \\ b \\ c \end{pmatrix}$ and $\begin{pmatrix} b \\ c \\ a \end{pmatrix},$ in degrees. -/
theorem calculus_23438 : IsGreatest {θ | ∃ (a b c : ℝ) (u v : EuclideanSpace ℝ (Fin 3)), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ θ ∈ Icc 0 π ∧ u = ![a, b, c] ∧ v = ![b, c, a] ∧ θ = InnerProductGeometry.angle u v} (120 * π / 180)  := by
  -- $2\pi / 3 \in [0, \pi]$
  have pipos : 0 < π := by
      exact pi_pos
  have piin : 120 * π / 180 ∈ Icc 0 π := by
    constructor
    linarith
    linarith
  -- $\cos(2\pi / 3) = -1/2$
  have cospieq : cos (π * (2 / 3)) = -1/2 := by
    have cospieq : cos (π * (2 / 3)) = - -(cos (π * (2 / 3))) := by
        ring
    rw [cospieq, ← Real.cos_pi_sub]
    ring_nf
    rw [mul_div, mul_one, Real.cos_pi_div_three]
    ring
  constructor
  · -- when $a = 1, b = 1, c = -2$, the angle between $u = ![a, b, c], v = ![b, c, a]$ is $120^{\circ}$
    use 1
    use 1
    use -2
    use ![1, 1, -2]
    use ![1, -2, 1]
    simp only [ne_eq, one_ne_zero, not_false_eq_true, neg_eq_zero, OfNat.ofNat_ne_zero, mem_Icc, Nat.succ_eq_add_one, Nat.reduceAdd, true_and]
    constructor
    exact piin
    let u : EuclideanSpace ℝ (Fin 3) := ![1, 1, -2]
    let v : EuclideanSpace ℝ (Fin 3) := ![1, -2, 1]
    have coseq := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
    simp only [EuclideanSpace.norm_eq, Nat.succ_eq_add_one, Nat.reduceAdd, norm_eq_abs, sq_abs, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, one_pow, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, even_two, Even.neg_pow, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_one, mul_neg, one_mul, u, v] at coseq
    norm_num at coseq
    ring_nf
    -- $\cos(\theta) = -1/2 = cos(2\pi / 3)$ and $\theta \in [0, \pi]$, so $\theta = 2\pi / 3$
    have anglein : InnerProductGeometry.angle u v ∈ Icc 0 π := by
      constructor
      exact InnerProductGeometry.angle_nonneg u v
      exact InnerProductGeometry.angle_le_pi u v
    have coseq2 : cos (InnerProductGeometry.angle u v) = cos (π * (2 / 3)) := by
      rw [cospieq]
      linarith
    ring_nf at piin
    apply Real.injOn_cos anglein piin at coseq2
    rw [coseq2]
  -- $2\pi / 3$ is the maximal such angle
  intro θ thetain
  rcases thetain with ⟨a, b, c, u, v, ane, _, _, thetain, ueq, veq, thetaeq⟩
  have coseq := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
  simp only [EuclideanSpace.norm_eq, Nat.succ_eq_add_one, Nat.reduceAdd, norm_eq_abs, sq_abs, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, one_pow, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, even_two, Even.neg_pow, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_one, mul_neg, one_mul, ueq, veq] at coseq
  ring_nf at coseq
  have sqsumpos : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by
    have lt : 0 < a ^ 2 := by
      exact pow_two_pos_of_ne_zero ane
    nlinarith
  rw [sq_sqrt (by linarith)] at coseq
  -- $-1 / 2 \leq \cos(\theta)$
  have cosge : -1 / 2 ≤ cos (InnerProductGeometry.angle u v) := by
    have le : a * b + a * c + b * c ≥ -(a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
      have le : 0 ≤ (a + b + c) ^ 2 := by
        exact sq_nonneg (a + b + c)
      linarith
    rw [← coseq] at le
    have le2 : -(a ^ 2 + b ^ 2 + c ^ 2) / 2 * (a ^ 2 + b ^ 2 + c ^ 2)⁻¹ ≤ cos (InnerProductGeometry.angle u v) * ((a ^ 2 + b ^ 2 + c ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2)⁻¹) := by
      rw [← mul_assoc, ueq, veq]
      refine (mul_le_mul_iff_of_pos_right ?_).mpr ?_
      exact inv_pos_of_pos sqsumpos
      exact le
    rw [mul_inv_cancel₀ (by exact Ne.symm (ne_of_lt sqsumpos)), mul_one, neg_div, neg_mul, div_eq_mul_inv, mul_comm, ← mul_assoc, inv_mul_cancel₀ (by exact Ne.symm (ne_of_lt sqsumpos))] at le2
    ring_nf at le2
    exact le2
  -- since $\theta \in [0, \pi]$, $theta \leq 2\pi / 3$
  rw [← cospieq] at cosge
  by_contra contra
  rw [not_le] at contra
  ring_nf at contra
  ring_nf at piin
  apply Real.strictAntiOn_cos piin thetain at contra
  rw [thetaeq] at contra
  linarith