import Mathlib

open Polynomial

/- 7. let $n \geq 2$ be a natural number. Show that the polynomial


$$

\left(x^{2}-1^{2}\right)\left(x^{2}-2^{2}\right)\left(x^{2}-3^{2}\right) \cdots\left(x^{2}-n^{2}\right)+1

$$


cannot be written as the product of two non-constant polynomials with whole coefficients.

## Solution -/
theorem algebra_262529 {n : ℕ} (hn : 2 ≤ n) :
    ¬∃ p q : Polynomial ℤ, 0 < p.natDegree ∧ 0 < q.natDegree ∧
      (∏ i ∈ Finset.Icc 1 n, (X ^ 2 - C ((i : ℤ) ^ 2)) + C 1 =
       p * q)
  := by
    -- Let p be the polynomial
    set p := ∏ i ∈ Finset.Icc 1 n, (X ^ 2 - C ((i : ℤ) ^ 2)) + C 1

    -- The degree of p is 2 * n
    have p_degree : p.natDegree = 2 * n := by
      unfold p
      -- we just sum each factor
      rw [Polynomial.natDegree_add_C, Polynomial.natDegree_prod]

      -- and each factor has a degree of two
      rw [Finset.sum_congr rfl <| fun x a => natDegree_X_pow_sub_C]

      -- So the sum is 2 * n
      simpa only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, smul_eq_mul] using Nat.mul_comm n 2
      -- and none of the factors are zero
      · simp only [Finset.mem_Icc, ne_eq, and_imp]
        intro n n1 n2
        refine X_pow_sub_C_ne_zero ?_ _
        decide

    -- assume the oppositve
    by_contra h

    -- then we have two polynomials r * s = p
    obtain ⟨r, s, hr, hs, hp⟩ := h

    -- degree of (r - s) ≤ 2*n - 1
    have r_sub_s_degree : (r - s).natDegree ≤ 2 * n - 1 := by
      -- degree of r - s is less than or equal to max (degree r) (degree s)
      refine le_trans (Polynomial.natDegree_sub_le r s) ?_

      -- we have degree p = degree r + degree s
      apply_fun (fun x => x.natDegree) at hp
      have r_ne : r ≠ 0 := ne_zero_of_natDegree_gt hr
      have s_ne : s ≠ 0 := ne_zero_of_natDegree_gt hs
      simp only [Polynomial.natDegree_mul r_ne s_ne] at hp

      -- but degree p = 2 * n
      rw [p_degree] at hp

      -- so because degree r and degree s are non-zero, we're done
      omega

    -- for k = -1, 1, -2, 2, ... -n, n we have p(k) = 1
    have eq_one : ∀ k : ℤ, k.natAbs ∈ Finset.Icc 1 n → p.eval k = 1 := by
      intro k kh
      unfold p
      -- we prove that the product is equal to zero
      simp only [eq_intCast, Int.cast_pow, Int.cast_natCast, Int.cast_one, eval_add, eval_one,
        add_left_eq_self]
      -- just one element has to be equal to zero
      rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]

      -- |k| works
      refine ⟨k.natAbs, kh, ?_⟩
      simp only [eval_sub, eval_pow, eval_X, eval_natCast, Int.natCast_natAbs, sq_abs, sub_self]

    -- Consider r ≠ s
    by_cases r_s : r - s ≠ 0
    -- -1, 1, ... , -n, n are roots of r - s
    · have roots_subs : Finset.Icc (-(n : ℤ)) (-1) ∪ Finset.Icc 1 n ⊆ (r - s).roots.toFinset := by
        -- let k be the element we'll prove is a root
        intro k k_mem
        -- |k| ∈ [1, n]
        have k_abs_mem : k.natAbs ∈ Finset.Icc 1 n := by
          simp only [Int.reduceNeg, Finset.mem_union] at k_mem
          obtain ⟨aa, bb⟩ := Int.eq_nat_or_neg k
          cases' bb with h1 h2
          · subst h1
            simp only [Int.natAbs_ofNat, Finset.mem_Icc]
            have not_neg : ¬((aa : ℤ) ≤ -1) := by linarith
            simpa only [Int.reduceNeg, Finset.mem_Icc, not_neg, and_false, Nat.one_le_cast,
              Nat.cast_le, false_or] using k_mem
          · subst h2
            have not_pos : ¬(1 ≤ -(aa : ℤ)) := by linarith
            simp only [Int.reduceNeg, Finset.mem_Icc, neg_le_neg_iff, Nat.cast_le, Nat.one_le_cast,
              not_pos, false_and, or_false] at k_mem
            simpa only [Int.reduceNeg, Finset.mem_Icc, neg_le_neg_iff, Nat.cast_le, Nat.one_le_cast,
              not_pos, false_and, or_false, Int.natAbs_neg, Int.natAbs_ofNat, Finset.mem_Icc] using k_mem.symm
        -- we just need to prove that eval k r - eval k s = 0
        simp only [Multiset.mem_toFinset, mem_roots', ne_eq, r_s, not_false_eq_true, IsRoot.def,
          eval_sub, true_and]

        -- we have that p = r * s
        apply_fun (fun x => x.eval k) at hp

        -- so (r * s) k = p k = 1
        rw [eq_one k k_abs_mem] at hp
        simp only [eval_mul] at hp
        -- but r k * s k = 1 means r k = s k
        exact Int.sub_eq_zero.mpr <| Int.eq_of_mul_eq_one hp.symm

      -- cardinality of -1, 1, ... , -n, n is 2 * n
      have roots_card_1 : (Finset.Icc (-(n : ℤ)) (-1) ∪ Finset.Icc 1 (n : ℤ)).card = 2 * n := by
        have disj : Disjoint (Finset.Icc (-(n : ℤ)) (-1)) (Finset.Icc 1 (n : ℤ)) := by
          refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
          convert_to ((Set.Icc (-(n : ℤ)) (-1) ∩ Set.Icc (1) (n : ℤ))).toFinset = ∅
          simp only [Int.reduceNeg, Set.toFinset_inter, Set.toFinset_Icc]
          rw [Set.toFinset_eq_empty, Set.Icc_inter_Icc]
          simp only [Int.reduceNeg, le_inf_iff, sup_le_iff, neg_le_neg_iff, Nat.one_le_cast,
            le_neg_self_iff, Int.reduceLE, and_false, neg_le_self_iff, Nat.cast_nonneg, true_and,
            false_and, not_false_eq_true, Set.Icc_eq_empty]
        simp only [Int.reduceNeg, disj, Finset.card_union_of_disjoint, Int.card_Icc, neg_add_cancel,
          sub_neg_eq_add, zero_add, Int.toNat_ofNat, add_sub_cancel_right]
        exact n.two_mul.symm

      -- then the number of roots isn't less than the degree
      have roots_not_le_degree : ¬↑(r - s).roots.card ≤ (r - s).degree := by
        simp only [not_le]
        calc (r - s).degree
        _ ≤ ↑(2 * n - 1) := natDegree_le_iff_degree_le.mp r_sub_s_degree
        _ < ↑(2 * n) := by
          norm_cast
          omega
        _ ≤ ↑(r - s).roots.card := by
          norm_cast
          exact le_trans (roots_card_1 ▸ Finset.card_le_card roots_subs) <| Multiset.toFinset_card_le (r - s).roots


      -- contradiction
      have r_sub_s_zero := Polynomial.card_roots.mt roots_not_le_degree
      contradiction
    -- then we have that r = s
    · simp only [ne_eq, Decidable.not_not] at r_s
      have eq : (r - s) + s = 0 + s := by
        exact congrFun (congrArg _ r_s) s
      simp only [sub_add_cancel, zero_add] at eq
      -- then p = r * r
      rw [eq.symm] at hp

      -- then p 0 is a square number
      have p_zero_square : IsSquare (p.eval 0)
        := ⟨r.eval 0, hp ▸ eval_mul⟩

      -- we can express it as square of a natural number
      have p_zero_square_nat : ∃ n : ℕ, p.eval 0 = (((n ^ 2) : ℕ) : ℤ) := by
        obtain ⟨z, zh⟩ := p_zero_square
        refine ⟨z.natAbs, ?_⟩
        simp only [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
        convert zh
        exact pow_two z

      -- we have that p 0 = (-1)^n * (n!)^2 + 1
      have p_zero : p.eval 0 = (-1) ^ n * (n.factorial) ^ 2 + 1 := by
        unfold p
        -- seperate product to LHS
        simp only [eq_intCast, Int.cast_pow, Int.cast_natCast, Int.cast_one, eval_add, eval_one,
          Int.reduceNeg, add_left_inj, Polynomial.eval_prod]

        -- Change terms x = --x
        convert_to ∏ j ∈ Finset.Icc 1 n, - -eval 0 (X ^ 2 - ↑j ^ 2) = (-1) ^ n * ↑n.factorial ^ 2
        simp only [eval_sub, eval_pow, eval_X, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, eval_natCast, zero_sub, neg_neg]

        -- Extract (-1) ^ n factor (using multiset lemmas)
        have prod_set_parity := ((Finset.Icc 1 n).1.map (fun j => -eval 0 ((X ^ 2 : ℤ[X] ) - (j : ℤ[X]) ^ 2))).prod_map_neg
        simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map,
          Function.comp_apply, Finset.prod_map_val, Int.reduceNeg, Multiset.card_map,
          Finset.card_val, Nat.card_Icc, add_tsub_cancel_right] at prod_set_parity
        rw [prod_set_parity]

        -- simplify
        simp only [Int.reduceNeg, eval_sub, eval_pow, eval_X, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, eval_natCast, zero_sub, neg_neg, mul_eq_mul_left_iff,
          pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, or_false]

        -- use ℕ
        norm_cast

        rw [Finset.prod_pow]
        congr
        -- use definion of factorial
        convert Finset.prod_Ico_id_eq_factorial n using 1

      -- n is even or odd
      cases' Nat.even_or_odd n with odd even
      -- when n is even: eval 0 p = n! ^ 2 + 1
      · simp only [Int.reduceNeg, odd, Even.neg_pow, one_pow, one_mul] at p_zero

        -- we have n! ^ 2 < p.eval 0 < (n! + 1) ^ 2
        have lower : (n.factorial) ^ 2 < p.eval 0 := by
          rw [p_zero]
          omega
        have upper : p.eval 0 < (n.factorial + 1) ^ 2 := by
          rw [p_zero]
          norm_cast
          simp only [add_pow_two, mul_one, one_pow, add_lt_add_iff_right, lt_add_iff_pos_right, Nat.ofNat_pos,
            mul_pos_iff_of_pos_left]
          positivity

        -- but we know that p = k ^ 2
        obtain ⟨k, hk⟩ := p_zero_square_nat
        rw [hk] at lower upper
        norm_cast at lower upper

        -- but there can't be a number strictly between successive numbers, contradiction
        have upp : n.factorial < k := (Nat.pow_lt_pow_iff_left (by decide)).mp lower
        have low : k < n.factorial + 1 := (Nat.pow_lt_pow_iff_left (by decide)).mp upper
        exact absurd low <| not_lt.mpr upp

      -- when n is odd, p 0 < 0
      · have neg : eval 0 p < 0 := by
          simpa only [p_zero, Int.reduceNeg, Odd.neg_one_pow even, neg_mul, one_mul,
            neg_add_lt_iff_lt_add, add_zero, one_lt_sq_iff_one_lt_abs, Nat.abs_cast,
            Nat.one_lt_cast, Nat.one_lt_factorial] using hn
        -- but if it's a square then it's positive, contradiction
        exact absurd neg <| not_lt.mpr <| IsSquare.nonneg p_zero_square