import Mathlib

open Real Set EuclideanSpace MeasureTheory
/-Let \[S_1 = \left\{ (x,y) \in \mathbb{R}^2 \mid\text{ and } \log_{10}(1 + x^2 + y^2) \leq 1 + \log_{10}(x + y) \right\}\] and \[S_2 = \left\{ (x,y) \in \mathbb{R}^2 \mid\log_{10}(2 + x^2 + y^2) \leq 2 + \log_{10}(x + y) \right\}.\]
What is the ratio of the area of $S_2$ to the area of $S_1$?
(A) $98$(B) $99$(C) $100$(D) $101$(E) $102$-/
theorem AMC_Algebra_97666 {S1 S2 : Set (EuclideanSpace ℝ (Fin 2))}
(hS1 : S1 = {pt : (EuclideanSpace ℝ (Fin 2)) | (0<pt 0 +pt 1) ∧ logb 10 (1 + (pt 0)^2 + (pt 1)^2) ≤ 1 + logb 10 (pt 0 + pt 1)})
(hS2 : S2 = {pt : (EuclideanSpace ℝ (Fin 2)) | 0< pt 0+pt 1 ∧ logb 10 (2 + (pt 0)^2 + (pt 1)^2) ≤ 2 + logb 10 (pt 0 + pt 1)}) :(MeasureTheory.volume S2).toReal/(MeasureTheory.volume S1).toReal = 102 := by
--We prove that $S_1$ is the closed ball of radius $7$ centered at $(5,5)$.
  have s1ball:S1=Metric.closedBall (!₂[(5:Real),5]) 7 :=by
    ext pt
    constructor
    --We prove that every point in $S_1$ is in the closed ball of radius $7$ centered at $(5,5)$.
    intro hpt
    rw[hS1] at hpt
    simp only [mem_setOf_eq] at hpt
    rw[←sub_le_iff_le_add,←logb_div] at hpt
    nth_rewrite 2[show 1=logb 10 10 by simp only [Nat.one_lt_ofNat,logb_self_eq_one]] at hpt
    rw[logb_le_logb,div_le_iff₀'] at hpt
    replace hpt:((pt 0)-5)^2+((pt 1)-5)^2≤7^2:=by
      linarith
    simp only [Metric.mem_closedBall, ge_iff_le]
    rw[EuclideanSpace.dist_eq]
    simp only [WithLp.equiv_symm_pi_apply, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,Matrix.cons_val_one, Matrix.head_cons]
    rw[sqrt_le_iff]
    simp only [Nat.ofNat_nonneg, Fin.isValue, true_and,dist,Fin.isValue, sq_abs]
    linarith
    all_goals
      try linarith
    field_simp;linarith;apply ne_of_gt;apply add_pos_of_pos_of_nonneg;apply add_pos_of_pos_of_nonneg
    simp only [one_pos]
    simp only [sq_nonneg]
    simp only [sq_nonneg]
    --We prove that every point in the closed ball of radius $7$ centered at $(5,5)$ is in $S_1$.
    intro hpt
    simp only [Metric.mem_closedBall,EuclideanSpace.dist_eq,Fin.isValue,WithLp.equiv_symm_pi_apply, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,Matrix.cons_val_one, Matrix.head_cons] at hpt
    apply sqrt_le_iff.mp at hpt
    simp only [Nat.ofNat_nonneg, Fin.isValue, true_and,dist_eq,sq_abs] at hpt
    simp only [sub_sq] at hpt
    replace hpt :1+(pt 0)^2+(pt 1)^2≤10*(pt 0 +pt 1):=by linarith
    have hpt2:0<pt 0+pt 1:=by nlinarith
    rw[hS1]
    simp only [mem_setOf_eq]
    constructor
    exact hpt2
    rw[←sub_le_iff_le_add,←logb_div]
    nth_rewrite 2[show 1=logb 10 10 by simp only [Nat.one_lt_ofNat,logb_self_eq_one]]
    rw[logb_le_logb,div_le_iff₀']
    all_goals
      try linarith
    field_simp;linarith;apply ne_of_gt;apply add_pos_of_pos_of_nonneg;apply add_pos_of_pos_of_nonneg;norm_num
    simp only [sq_nonneg]
    simp only [sq_nonneg]
  --We prove that S2 is the closed ball of radius $7\sqrt{102}$ centered at $(50,50)$.
  have s2ball:S2=Metric.closedBall (!₂[(50:Real),50]) (7*sqrt 102) :=by
    ext pt
    simp only [Metric.mem_closedBall, ge_iff_le]
    constructor
    --We prove that every point in $S_2$ is in the closed ball of radius $7\sqrt{102}$ centered at $(50,50)$.
    intro hpt
    rw[hS2] at hpt
    simp only [mem_setOf_eq] at hpt
    rw[←sub_le_iff_le_add,←logb_div] at hpt
    rw[logb_le_iff_le_rpow,div_le_iff₀'] at hpt
    replace hpt:((pt 0)-50)^2+((pt 1)-50)^2≤(7*sqrt 102)^2:=by
      rw[mul_pow,sq_sqrt]
      linarith
      norm_num
    rw[EuclideanSpace.dist_eq]
    simp only [WithLp.equiv_symm_pi_apply, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,Matrix.cons_val_one, Matrix.head_cons]
    rw[sqrt_le_iff]
    simp only [Nat.ofNat_nonneg, Fin.isValue, true_and,dist,Fin.isValue, sq_abs]
    norm_num
    all_goals
      try linarith
    field_simp;linarith;apply ne_of_gt;apply add_pos_of_pos_of_nonneg;apply add_pos_of_pos_of_nonneg
    simp only [two_pos]
    simp only [sq_nonneg]
    simp only [sq_nonneg]
    --We prove that every point in the closed ball of radius $7\sqrt{102}$ centered at $(50,50)$ is in $S_2$.
    intro hpt
    simp only [Metric.mem_closedBall,EuclideanSpace.dist_eq,Fin.isValue,WithLp.equiv_symm_pi_apply, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,Matrix.cons_val_one, Matrix.head_cons] at hpt
    rw[sqrt_le_iff,mul_pow,sq_sqrt,dist_eq,dist_eq,sq_abs,sq_abs] at hpt
    simp only [hS2, Fin.isValue, mem_setOf_eq]
    replace hpt :2+(pt 0)^2+(pt 1)^2≤100*(pt 0 +pt 1):=by
      ring_nf at hpt
      linarith
    have hpt2:0<pt 0+pt 1:=by nlinarith
    constructor
    exact hpt2
    rw[←sub_le_iff_le_add,←logb_div,logb_le_iff_le_rpow,div_le_iff₀']
    linarith
    all_goals
      try linarith
    apply div_pos _ hpt2
    swap
    apply ne_of_gt
    all_goals
      apply add_pos_of_pos_of_nonneg
      apply add_pos_of_pos_of_nonneg
      simp only [two_pos];simp only [sq_nonneg];simp only [sq_nonneg]
  rw[s1ball,s2ball]
--We calculate the volume of the closed ball of radius $7$ centered at $(5,5)$ and the volume of the closed ball of radius $7\sqrt{102}$ centered at $(50,50)$.
  rw[EuclideanSpace.volume_closedBall,EuclideanSpace.volume_closedBall]
  simp only [ENNReal.ofReal_ofNat, Fintype.card_fin, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero,not_false_eq_true, div_self, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, sqrt_nonneg, ENNReal.toReal_ofReal]
--We calculate the ratio of the volumes.
  field_simp
  rw[mul_pow,sq_sqrt]
  norm_num
  ring_nf
  norm_num