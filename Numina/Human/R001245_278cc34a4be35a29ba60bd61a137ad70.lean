import Mathlib

open Matrix

/- Find the matrix $\mathbf{P}$ such that for any vector $\mathbf{v},$ $\mathbf{P} \mathbf{v}$ is the projection of $\mathbf{v}$ onto the $y$-axis. -/
theorem calculus_22005 (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP : ∀ v : Matrix (Fin 3) (Fin 1) ℝ, P * v = (v 1) • ![0, 1, 0]) :
    P = !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
  -- $P * [1, 0, 0] = [0, 0, 0]$
  have h1 := hP ![1, 0, 0]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_one, head_cons, zero_smul] at h1
  -- $P * [0, 1, 0] = [0, 1, 0]$
  have h2 := hP ![0, 1, 0]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_one, head_cons, one_smul] at h2
  -- $P * [0, 0, 1] = [0, 0, 0]$
  have h3 := hP ![0, 0, 1]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_one, head_cons, zero_smul] at h3
  -- to prove $P = !![0, 0, 0; 0, 1, 0; 0, 0, 0]$, we prove that the $(i, j)$th entry of both sides coincide
  ext i j
  fin_cases j
  · -- when $j = 0$
    simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, vecCons_const]
    have eqi0 := congrFun (congrFun h1 i) 0
    simp only [Fin.isValue, mul_apply', cons_val', Pi.one_apply, Pi.zero_apply, empty_val', cons_val_fin_one, vecCons_const, dotProduct_cons, vecHead, mul_one, dotProduct_zero', add_zero] at eqi0
    exact eqi0
  · -- when $j = 1$
    fin_cases i
    · -- when $i = 0$
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one, head_cons, empty_val', cons_val_fin_one, cons_val_zero]
      have eq01 := congrFun (congrFun h2 0) 1
      simp only [Fin.isValue, mul_apply', cons_val', Pi.zero_apply, Pi.one_apply, empty_val', cons_val_fin_one, dotProduct_cons, vecHead, mul_zero, vecTail, Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, mul_one, dotProduct_zero', add_zero, zero_add, cons_val_zero] at eq01
      exact eq01
    · -- when $i = 1$
      simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, head_cons, empty_val', cons_val_fin_one]
      have eq11 := congrFun (congrFun h2 1) 1
      simp only [Fin.isValue, mul_apply', cons_val', Pi.zero_apply, Pi.one_apply, empty_val', cons_val_fin_one, dotProduct_cons, vecHead, mul_zero, vecTail, Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, mul_one, dotProduct_zero', add_zero, zero_add, cons_val_one, cons_val_zero] at eq11
      exact eq11
    · -- when $i = 2$
      simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, head_cons, empty_val', cons_val_fin_one, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_fin_const]
      have eq21 := congrFun (congrFun h2 2) 1
      simp only [Fin.isValue, mul_apply', cons_val', Pi.zero_apply, Pi.one_apply, empty_val', cons_val_fin_one, dotProduct_cons, vecHead, mul_zero, vecTail, Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, mul_one, dotProduct_zero', add_zero, zero_add, cons_val_two, cons_val_one] at eq21
      exact eq21
  -- when $j = 2$
  simp only [Fin.reduceFinMk, Fin.isValue, of_apply, cons_val', cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons, empty_val', cons_val_fin_one, vecCons_const]
  have eqi2 := congrFun (congrFun h3 i) 2
  simp only [Fin.isValue, mul_apply', dotProduct, cons_val', Pi.zero_apply, Pi.one_apply, empty_val', cons_val_fin_one, Fin.sum_univ_three, cons_val_zero, mul_zero, cons_val_one, vecHead, add_zero, cons_val_two, vecTail, Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, mul_one, zero_add] at eqi2
  exact eqi2