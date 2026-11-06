import Mathlib

open Polynomial

/- $4 \cdot 77$ Given three quadratic trinomials:

$$

\begin{array}{l}
p_{1}(x)=x^{2}+p_{1} x+q_{1}, \\
p_{2}(x)=x^{2}+p_{2} x+q_{2}, \\
p_{3}(x)=x^{2}+p_{3} x+q_{3} .
\end{array}

$$


Prove that the equation $\left|p_{1}(x)\right|+\left|p_{2}(x)\right|=\left|p_{3}(x)\right|$ has at most 8 roots. -/
theorem algebra_214309 (p1 p2 p3 q1 q2 q3 : ℝ) :
    {x : ℝ | abs (x ^ 2 + p1 * x + q1) + abs (x ^ 2 + p2 * x + q2) = abs (x ^ 2 + p3 * x + q3)}.encard ≤ 8
  := by
    -- Let the polynomials be P1 P2 P3
    let P1 : ℝ[X] := X ^ 2 + (C p1) * X + C q1
    let P2 : ℝ[X] := X ^ 2 + (C p2) * X + C q2
    let P3 : ℝ[X] := X ^ 2 + (C p3) * X + C q3
    convert_to {x | |P1.eval x| + |P2.eval x| = |P3.eval x|}.encard ≤ 8
    · congr
      ext x
      unfold P1 P2 P3
      simp only [Set.mem_setOf_eq, eval_add, eval_pow, eval_X, eval_mul, eval_C]

    -- Rewrite equation to equal 0
    convert_to {x | |P1.eval x| + |P2.eval x| - |P3.eval x| = 0}.encard ≤ 8
    · congr
      ext x
      exact Iff.symm sub_eq_zero

    -- We can split into sign cases, to get rid of abs
    have split : {x | |eval x P1| + |eval x P2| - |eval x P3| = 0}
      ⊆ {x |  (1) * eval x P1 +  (1) * eval x P2 - eval x P3 = 0}
      ∪ {x |  (1) * eval x P1 + (-1) * eval x P2 - eval x P3 = 0}
      ∪ {x | (-1) * eval x P1 +  (1) * eval x P2 - eval x P3 = 0}
      ∪ {x | (-1) * eval x P1 + (-1) * eval x P2 - eval x P3 = 0} := by
        intro x
        simp only [Set.mem_setOf_eq, Set.mem_union, one_mul, neg_mul]
        intro h
        cases' le_total 0 (eval x P1) with pos1 neg1
        · cases' le_total 0 (eval x P2) with pos2 neg2
          · cases' le_total 0 (eval x P3) with pos3 neg3
            · simp only [abs_of_nonneg, pos1, pos2, pos3] at h
              exact Or.inl <| Or.inl <| Or.inl h
            · simp only [abs_of_nonneg, abs_of_nonpos, pos1, pos2, neg3] at h
              convert Or.inr (zero_eq_neg.mpr h).symm using 2
              · ring
          · cases' le_total 0 (eval x P3) with pos3 neg3
            · simp only [abs_of_nonneg, abs_of_nonpos, pos1, neg2, pos3] at h
              exact Or.inl <| Or.inl <| Or.inr h
            · simp only [abs_of_nonneg, abs_of_nonpos, pos1, neg2, neg3] at h
              convert Or.inl <| Or.inr (zero_eq_neg.mpr h).symm using 3
              · ring
        · cases' le_total 0 (eval x P2) with pos2 neg2
          · cases' le_total 0 (eval x P3) with pos3 neg3
            · simp only [abs_of_nonneg, abs_of_nonpos, neg1, pos2, pos3] at h
              exact Or.inl <| Or.inr h
            · simp only [abs_of_nonneg, abs_of_nonpos, neg1, pos2, neg3] at h
              convert Or.inl <| Or.inl <| Or.inr (zero_eq_neg.mpr h).symm using 4
              · ring
          · cases' le_total 0 (eval x P3) with pos3 neg3
            · simp only [abs_of_nonneg, abs_of_nonpos, neg1, neg2, pos3] at h
              exact Or.inr h
            · simp only [abs_of_nonneg, abs_of_nonpos, neg1, neg2, neg3] at h
              convert Or.inl <| Or.inl <| Or.inl (zero_eq_neg.mpr h).symm using 4
              · ring

    -- Combine P1 P2 P3 into one polynomial
    have as_eval : ∀ a b, {x | a * eval x P1 + b * eval x P2 - eval x P3 = 0}
      ⊆ {x | eval x (C a * P1 + C b * P2 - P3) = 0} := by
        intro a b c x
        simpa only [eval_sub, eval_add, eval_mul, eval_C, Set.mem_setOf_eq] using x

    -- coefficient of X ^ 2 is 1 in P1, P2 and P3
    have ⟨coeff_1, coeff_2, coeff_3⟩ : P1.coeff 2 = 1 ∧ P2.coeff 2 = 1 ∧ P3.coeff 2 = 1 := by
      unfold P1 P2 P3
      simp only [coeff_add, coeff_X_pow, ↓reduceIte, coeff_mul_X, coeff_C_succ, add_zero, and_self]

    -- Our sets are rootsets
    have as_rootset : ∀ a b : ℝ, a + b - 1 ≠ 0 → {x | eval x (C a * P1 + C b * P2 - P3) = 0}
      = (C a * P1 + C b * P2 - P3).rootSet ℝ := by
        intro a b h
        ext x
        rw [Polynomial.mem_rootSet_of_ne]
        simp only [eval_sub, eval_add, eval_mul, eval_C, Set.mem_setOf_eq, coe_aeval_eq_eval]
        by_contra eq_zero
        apply_fun (fun p => p.coeff 2) at eq_zero
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_1, mul_one, coeff_2, coeff_3,
          coeff_zero] at eq_zero
        exact h eq_zero

    -- The polynomials have degree 2
    have degree_Pk : ∀ pk qk : ℝ, (X ^ 2 + C pk * X + C qk).natDegree = 2 := by
      intro pk qk
      simp only [natDegree_add_C]
      -- the degree is less than or equal to 2, and X ^ 2 has a non-zero coefficient
      refine eq_natDegree_of_le_mem_support ?_ ?_
      have left : (X ^ 2 : ℝ[X]).natDegree ≤ 2 := natDegree_X_pow_le 2
      have right : (C pk * X : ℝ[X]).natDegree ≤ 2 := by
        by_cases hp : pk = 0
        · simp only [hp, map_zero, zero_mul, natDegree_zero, zero_le]
        · rw [Polynomial.natDegree_C_mul_X _ hp]
          linarith only
      exact (Polynomial.natDegree_add_le_iff_left _ _ right).mpr left
      simp only [mem_support_iff, coeff_add, coeff_X_pow, ↓reduceIte, coeff_mul_X, coeff_C_succ,
        add_zero, ne_eq, one_ne_zero, not_false_eq_true]
    have degree_P1 : P1.natDegree = 2 := degree_Pk p1 q1
    have degree_P2 : P2.natDegree = 2 := degree_Pk p2 q2
    have degree_P3 : P3.natDegree = 2 := degree_Pk p3 q3

    -- Combined polynomial has at most 2 roots
    have roots_card : ∀ a b, ((C a * P1 + C b * P2 - P3).rootSet ℝ).encard ≤ 2 := by
      intro a b
      -- It's upper bounded by (C a * P1 + C b * P2 - P3).roots, which contains duplicates
      rw [Polynomial.rootSet]
      simp only [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le_ofNat]
      rw [Polynomial.aroots_def]
      simp only [Algebra.id.map_eq_id, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
        map_C, RingHom.id_apply, map_id]
      refine le_trans (Multiset.toFinset_card_le _) ?_

      -- the number of roots is at most the degree
      refine le_trans (Polynomial.card_roots' _) ?_
      -- degree of a * P1 + b * P2 - P3 is at most two, because each Pk is at most degree two
      refine (Polynomial.natDegree_sub_le_iff_left ?_).mpr ?_
      exact Nat.le_of_eq degree_P3
      refine (Polynomial.natDegree_add_le_iff_left _ _ ?_).mpr ?_
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) <| Nat.le_of_eq degree_P2
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) <| Nat.le_of_eq degree_P1

    -- We have enough info to chain inequalities
    calc {x | |eval x P1| + |eval x P2| - |eval x P3| = 0}.encard
    _ ≤ ({x | 1 * eval x P1 + 1 * eval x P2 - eval x P3 = 0}
    ∪ {x | 1 * eval x P1 + -1 * eval x P2 - eval x P3 = 0}
    ∪ {x | -1 * eval x P1 + 1 * eval x P2 - eval x P3 = 0}
    ∪ {x | -1 * eval x P1 + -1 * eval x P2 - eval x P3 = 0}).encard
      -- split up into sign cases
      := Set.encard_le_card split
    _ ≤ ({x | eval x (C 1 * P1 + C 1 * P2 - P3) = 0}
    ∪ {x | eval x (C 1 * P1 + C (-1) * P2 - P3) = 0}
    ∪ {x | eval x (C (-1) * P1 + C 1 * P2 - P3) = 0}
    ∪ {x | eval x (C (-1) * P1 + C (-1) * P2 - P3) = 0}).encard := by
      refine Set.encard_le_card ?_
      -- each LHS part is a subset of each RHS part
      refine Set.union_subset_union ?_ (as_eval (-1) (-1))
      refine Set.union_subset_union ?_ (as_eval (-1) 1)
      exact Set.union_subset_union (as_eval 1 1) (as_eval 1 (-1))
    _ = (((C 1 * P1 + C 1 * P2 - P3).rootSet ℝ)
    ∪ ((C 1 * P1 + C (-1) * P2 - P3).rootSet ℝ)
    ∪ ((C (-1) * P1 + C 1 * P2 - P3).rootSet ℝ)
    ∪ ((C (-1) * P1 + C (-1) * P2 - P3).rootSet ℝ)).encard := by
      -- rewrite as rootsets
      congr
      all_goals exact as_rootset _ _ (by linarith only)
    _ ≤ ((C 1 * P1 + C 1 * P2 - P3).rootSet ℝ).encard
    + ((C 1 * P1 + C (-1) * P2 - P3).rootSet ℝ).encard
    + ((C (-1) * P1 + C 1 * P2 - P3).rootSet ℝ).encard
    + ((C (-1) * P1 + C (-1) * P2 - P3).rootSet ℝ).encard := by
      -- cardinality is largest if they are all disjoint
      refine le_trans (Set.encard_union_le _ _) ?_
      apply add_le_add_right
      refine le_trans (Set.encard_union_le _ _) ?_
      apply add_le_add_right
      exact Set.encard_union_le _ _
    _ ≤ 2 + 2 + 2 + 2 := by
      -- every case has at most two roots
      gcongr
      all_goals exact roots_card _ _

    -- and 4 * 2 = 8, so 8 is our upper bound
    _ = 8 := by ring