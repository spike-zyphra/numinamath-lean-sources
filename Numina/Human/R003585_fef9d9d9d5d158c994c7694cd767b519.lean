import Mathlib

/- AM-GM inequality variant for a finite number of real non-negative variables. -/
lemma Fin_geom_mean_le_arith_mean {n : ℕ} [NeZero n]
  {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
  : n * (∏ j, a j) ^ (1 / n : ℝ) ≤ ∑ j, a j := by

    -- apply AM-GM to a, where equal weights of (1 / n)
    have am_gm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 / n : ℝ)) a
      (fun _ _ => Nat.one_div_cast_nonneg n) (by norm_num) (fun i a => ha i)

    -- the weights sum to 1
    have weights_sum_one : (∑ i : Fin n, (fun x => (1 / n : ℝ)) i) = 1 := by norm_num

    -- simplify AM-GM
    norm_num [weights_sum_one, ←Finset.mul_sum] at am_gm

    -- n is positive
    have n_pos : (0 : ℝ) < n := by norm_num [Nat.pos_of_neZero n]

    -- multiply both sides by n
    replace am_gm := (mul_le_mul_left n_pos).mpr am_gm

    -- we have the desired inequality
    convert am_gm
    -- lhs is equal
    -- power distributes over product
    · rw [Real.finset_prod_rpow]
      norm_num
      · norm_num [ha]
    -- rhs is equal
    · field_simp

/- Example 4 Let $a_{1}, a_{2}, \cdots, a_{n} \in \mathbf{R}^{+}$, and $a_{1}+a_{2}+\cdots+a_{n}<1$, prove:

$$

\frac{a_{1} a_{2} \cdots a_{n}\left[1-\left(a_{1}+a_{2}+\cdots+a_{n}\right)\right]}{\left(a_{1}+a_{2}+\cdots+a_{n}\right)\left(1-a_{1}\right)\left(1-a_{2}\right) \cdots\left(1-a_{n}\right)} \leqslant \frac{1}{n^{n+1}} .

$$
 -/
theorem inequalities_198943 {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (h : ∑ i, a i < 1) :
    ((∏ i, a i) * (1 - ∑ j, a j)) / ((∑ j, a j) * ∏ i, (1 - a i)) ≤ 1 / (n ^ (n + 1)) := by
      -- consider when n is 0
      by_cases hn : n = 0
      -- then it's trivial
      · subst hn
        norm_num

      -- so let n ≠ 0
      have n_not_zero : NeZero n := { out := hn }

      -- let a_(n+1) be 1 - ∑ a i
      let a_last := 1 - ∑ i, a i

      -- which is positive
      have a_last_pos : 0 < a_last := by
        unfold a_last
        linarith

      -- then we add a_(n+1) to the sequence of a, call this new sequence a'
      let a' : Fin (n+1) → ℝ := Fin.cons a_last a

      -- We have (∏ a i) * (1 - ∑ a i) = ∏ a' i
      have a'_prod : (∏ i, a i) * (1 - ∑ j, a j) = ∏ i, a' i := by
          unfold a' a_last
          rw [Fin.prod_cons]
          ring

      -- We have (∑ a i) * ∏ (1 - a i) = ∏ (1 - a' i)
      have a'_prod_one_sub : (∑ i, a i) * ∏ i, (1 - a i) = ∏ i, (1 - a' i) := by
        convert_to _ = ∏ i, ((1 - ·) ∘ a') i
        unfold a' a_last
        rw [Fin.comp_cons]
        rw [Fin.prod_cons]
        norm_num

      -- simplify inequality using a', removing a
      rw [a'_prod, a'_prod_one_sub]

      -- the product ∏ (1 - a' i) is positive
      have a'_prod_pos : 0 < ∏ i, (1 - a' i) := by
        -- every term is positive
        apply Finset.prod_pos
        norm_num
        intro i
        unfold a'
        -- check a_(n+1) and a values separately
        induction' i using Fin.cases with h1
        · norm_num [a_last]
          refine Finset.sum_pos ?_ Finset.univ_nonempty
          norm_num
          exact ha
        · norm_num
          refine lt_of_le_of_lt ?_ h
          rw [←Finset.sum_singleton a h1]
          refine Finset.sum_le_univ_sum_of_nonneg ?_
          exact (le_of_lt <| ha ·)

      -- n ^ (n + 1) is positive
      have n_pow : (0 : ℝ) < n ^ (n + 1) := by positivity

      -- rewrite to get rid of division in inequality
      rw [div_le_div_iff₀ a'_prod_pos n_pow]
      norm_num

      -- sum of a' is equal to 1
      have a'_sum_eq_one : ∑ j, a' j = 1 := by
        unfold a'
        rw [Fin.sum_cons]
        unfold a_last
        ring

      -- for every i, `1 - a' i = a'_1 + a'_2 + ... + a'_(i-1) + a'_(i+1) + ... + a'_(n+1)`
      have one_sub_a' : ∀ i, 1 - a' i = ∑ j, (Fin.removeNth i a') j := by
        intro i
        rw [←a'_sum_eq_one, Fin.sum_univ_succAbove _ i]
        norm_num [Fin.removeNth]

      -- every a' is positive
      have ha' : ∀ i, 0 < a' i := by
        intro i
        induction' i using Fin.cases with h1
        · simpa only [a', Fin.cons_zero] using a_last_pos
        · simpa only [a', Fin.cons_succ] using ha h1

      -- using AM-GM we have,for every i, `n * (a'_1 * a'_2 * ... * a'_(i-1) * a'_(i+1) * ... * a'_(n+1)) ^ (1 / n)`
      -- `≤ a'_1 + a'_2 + ... + a'_(i-1) + a'_(i+1) + ... + a'_(n+1)`
      have one_sub_a'_le : ∀ i, n * (∏ j, (Fin.removeNth i a') j) ^ (1 / n : ℝ) ≤ ∑ j, (Fin.removeNth i a') j := by
        intro i
        refine @Fin_geom_mean_le_arith_mean n _ (i.removeNth a') ?_
        norm_num [Fin.removeNth]
        intro j
        exact le_of_lt (ha' (i.succAbove j))

      -- for every i, we have `(a'_1 * a'_2 * ... * a'_(i-1) * a'_(i+1) * ... * a'_(n+1)) = (∏ j, a' j) / a' i`
      have prod_eq : ∀ i, ∏ j, i.removeNth a' j = (∏ j, a' j) / a' i := by
        unfold Fin.removeNth
        intro i
        rw [Fin.prod_univ_succAbove _ i]
        refine Eq.symm (mul_div_cancel_left₀ _ ?_)
        exact (ne_of_lt (ha' i)).symm

      -- product of a' values is positive, because every a' is positive
      have a'_prod_pos : 0 < ∏ j, a' j := Finset.prod_pos fun i a => ha' i

      -- so we have `∏ i, n * ((∏ a' j) / a' i) ^ (1 / n) ≤ ∏ (1 - a' i)`
      have prod_sub_le : ∏ i, n * ((∏ j, a' j) / a' i) ^ (1 / n : ℝ) ≤ ∏ i, (1 - a' i) := by
        apply Finset.prod_le_prod
        · intro i hi
          have a'_i_pos : 0 < a' i := ha' i
          positivity
        · intro i hi
          rw [←prod_eq, one_sub_a']
          exact one_sub_a'_le i

      -- we have the inequality, but the LHS is in a more complicated form
      convert prod_sub_le
      -- show LHS is equal
      -- simplify nested product
      · rw [←Finset.pow_card_mul_prod, Real.finset_prod_rpow]
        simp only [Finset.card_univ, Fintype.card_fin, Finset.prod_div_distrib, Finset.prod_const,
          one_div]

        -- product of a' terms is not zero, because it's positive
        have a'_prod_ne_zero : ∏ i, a' i ≠ 0 := (ne_of_lt a'_prod_pos).symm

        -- so we can cancel a (∏ a' i)
        have cancel_pow : (∏ i, a' i) ^ (n + 1) / (∏ i, a' i) = (∏ i, a' i) ^ n
          := div_eq_of_eq_mul a'_prod_ne_zero rfl

        rw [cancel_pow]

        -- simplify powers
        rw [←Real.rpow_natCast _ n, Real.rpow_rpow_inv]

        -- reorder terms
        ring
        -- our transformations were valid because everything positive
        · positivity
        · positivity
        · intro i hi
          have den_pos : 0 < a' i := ha' i
          positivity