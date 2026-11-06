import Mathlib

open Polynomial

/- $P(x)$ is a polynomial such that when $P(x)$ is divided by $x-13$ the remainder is $19$, and when $P(x)$ is divided by $x+17$ the remainder is $-11$. What is the remainder when $P(x)$ is divided by $(x-13)(x+17)$? -/
theorem algebra_21488 {P : Polynomial ℝ} (hP1 : P % (X - C 13) = C 19) (hP2 : P % (X + C 17) = C (-11)) :
    P % ((X - C 13) * (X + C 17)) = X + C 6 := by
  have degeq : ((X - C 13) * (X + C 17) : ℝ[X]).natDegree = 2 := by
    rw [natDegree_mul]
    simp only [natDegree_sub_C, natDegree_X, natDegree_add_C, Nat.reduceAdd]
    exact X_sub_C_ne_zero 13
    exact X_add_C_ne_zero 17
  -- the degree of $P$ is less than $2$, so $P % (x-13)(x+17) = ax + b$
  have degle : (P % ((X - C 13) * (X + C 17))).natDegree < ((X - C 13) * (X + C 17) : ℝ[X]).natDegree := by
    have natDegree_mod_lt (p : Polynomial ℝ) {q : Polynomial ℝ} (hq : q.natDegree ≠ 0) :
      (p % q).natDegree < q.natDegree := by
      have hq' : q.leadingCoeff ≠ 0 := by
        rw [leadingCoeff_ne_zero]
        contrapose! hq
        simp [hq]
      rw [mod_def]
      refine (natDegree_modByMonic_lt p ?_ ?_).trans_le ?_
      · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
        rw [mul_inv_eq_one₀ hq']
      · contrapose! hq
        rw [← natDegree_mul_C_eq_of_mul_eq_one ((inv_mul_eq_one₀ hq').mpr rfl)]
        simp [hq]
      · exact natDegree_mul_C_le q q.leadingCoeff⁻¹
    refine natDegree_mod_lt P ?_
    rw [degeq]
    norm_num
  rw [degeq] at degle
  apply Nat.le_of_lt_succ at degle
  have Premeq := eq_X_add_C_of_natDegree_le_one degle
  have Peq: P = ((X - C 13) * (X + C 17)) * (P / ((X - C 13) * (X + C 17))) + P % ((X - C 13) * (X + C 17)) := by
    exact Eq.symm (EuclideanDomain.div_add_mod P ((X - C 13) * (X + C 17)))
  rw [Premeq] at Peq
  have Peq2 := Peq
  rw [mod_X_sub_C_eq_C_eval, C_inj] at hP1
  rw [← sub_neg_eq_add, ← map_neg, mod_X_sub_C_eq_C_eval, C_inj] at hP2
  -- $P(13) = 13a + b=19$
  apply congrArg (fun x ↦ (eval (13 : ℝ)) x) at Peq
  rw [hP1] at Peq
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, zero_add] at Peq
  -- $P(-17)=-17a+b=-11$
  apply congrArg (fun x ↦ (eval (-17 : ℝ)) x) at Peq2
  rw [hP2] at Peq2
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, neg_add_cancel, mul_zero, zero_mul, mul_neg, zero_add] at Peq2
  -- so $a = 1, b = 6$
  have aeq : (P % ((X - C 13) * (X + C 17))).coeff 1 = 1 := by
    linarith
  have beq : (P % ((X - C 13) * (X + C 17))).coeff 0 = 6 := by
    linarith
  rw [Premeq, aeq, beq, map_one, one_mul]