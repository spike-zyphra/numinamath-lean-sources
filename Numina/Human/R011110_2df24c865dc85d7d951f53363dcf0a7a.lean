import Mathlib

set_option maxRecDepth 10000

/- Task B-3.5. A group of children were competing who would eat more strawberries. The winner ate $n$ strawberries, and each subsequent one ate two strawberries less, all the way to the last child in the $k$-th place, who ate $n+2-2k$ strawberries. The total number of strawberries eaten in the competition is 2014. How many strawberries did the winner eat at least? -/
theorem algebra_222271
  : IsLeast ({n : ℕ | ∃ (k : ℕ+) (f : Fin k → ℕ), f 0 = n ∧ (∀ i, f i = n - 2 * i) ∧ ∑ i : Fin k, f i = 2014}) 90
  := by
    -- inline the function f
    have set_eq_1 : {n : ℕ | ∃ (k : ℕ+) (f : Fin k → ℕ), f 0 = n ∧ (∀ i, f i = n - 2 * i) ∧ ∑ i : Fin k, f i = 2014}
      = {n : ℕ | ∃ (k : ℕ+), ∑ i : Fin k, (n - 2 * i) = 2014} := by
        ext n
        simp only [Set.mem_setOf_eq]
        constructor
        · intro ⟨k, f, h1, h2, h3⟩
          exists k
          simp_rw [h2] at h3
          exact h3
        · intro ⟨k, h3⟩
          exists k, (n - 2 * ·)
          simp only [Fin.val_zero, mul_zero, tsub_zero, implies_true, true_and]
          exact h3

    rw [set_eq_1]

    -- if we have a valid sum, we can truncate it to focus on only positive terms
    have lesser_sum : ∀ {n : ℕ} {k : ℕ+}, ∑ i : Fin k, (n - 2 * i) = 2014
      → ∃ (k' : ℕ+), 2 * (k' - 1) < n ∧ ∑ i : Fin k', (n - 2 * i) = 2014 ∧ ∀ i : Fin k', 0 < (n - 2 * i) := by
      intro n k sum

      -- let n = 0
      by_cases hn : n = 0
      -- then we can't have given out 2014 strawberries, contradiction
      · rw [hn] at sum
        norm_num at sum
      -- so n ≠ 0

      by_cases h : 2 * (k - 1) < n
      · exact ⟨k, h, sum, by omega⟩
      · exists (⟨(n+1) / 2, ?_⟩)
        · simp only [Nat.div_pos_iff, Nat.ofNat_pos, Nat.reduceLeDiff, true_and]
          exact Nat.one_le_iff_ne_zero.mpr hn
        simp only [PNat.mk_coe, Nat.add_one_sub_one, id_eq, ne_eq, eq_mpr_eq_cast, tsub_pos_iff_lt]
        split_ands
        · omega
        · convert sum using 1
          simp only [not_lt] at h
          rw [←Finset.sum_range (fun x => (n - 2 * x))]
          rw [←Finset.sum_range (fun x => (n - 2 * x))]
          apply Finset.sum_subset_zero_on_sdiff
          · gcongr
            omega
          · simp only [Finset.mem_sdiff, Finset.mem_range, not_lt, and_imp]
            omega
          · norm_num
        · omega

    -- so wlog, we can focus on the cases where everyone gets aleast one strawberry, i.e. 2 * (k - 1) < n
    have non_empty : {n : ℕ | ∃ (k : ℕ+), ∑ i : Fin k, (n - 2 * i) = 2014}
      = {n : ℕ | ∃ (k' : ℕ+), 2 * (k' - 1) < n ∧ ∑ i : Fin k', (n - 2 * i) = 2014 ∧ ∀ i : Fin k', 0 < (n - 2 * i)} := by
        ext n
        simp only [Set.mem_setOf_eq]
        constructor
        · intro ⟨k, kh⟩
          exact lesser_sum kh
        · intro ⟨k', k_le, k_sum, k_pos⟩
          exists k'

    rw [non_empty]

    -- consider the values of n and k as pairs
    have as_pair : {n : ℕ | ∃ (k' : ℕ+), 2 * (k' - 1) < n ∧ ∑ i : Fin k', (n - 2 * i) = 2014 ∧ ∀ i : Fin k', 0 < (n - 2 * i)}
      = (Prod.fst '' {(n, k') : ℕ × ℕ+ | 2 * (k' - 1) < n ∧ ∑ i : Fin k', (n - 2 * i) = 2014 ∧ ∀ i : Fin k', 0 < (n - 2 * i)}) := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists, exists_and_right,
          exists_eq_right]

    rw [as_pair]

    -- consider the sum as a sum over integers
    have as_int : {(n, k') : ℕ × ℕ+ | 2 * (k' - 1) < n ∧ ∑ i : Fin k', (n - 2 * i) = 2014 ∧ ∀ i : Fin k', 0 < (n - 2 * i)}
      = {(n, k') : ℕ × ℕ+ | 2 * (k' - 1) < n ∧ ∑ i : Fin k', ((n : ℤ) - 2 * (i : ℤ)) = 2014 ∧ ∀ i : Fin k', 0 < (n - 2 * i)} := by
        ext ⟨n, k'⟩
        simp only [Set.mem_setOf_eq, and_congr_right_iff, and_congr_left_iff]
        intro aa bb

        have distrib_cast : ∀ i : Fin k', (((n - 2 * i) : ℕ) : ℤ) = (n : ℤ) - ((2 * i : ℕ) : ℤ) := by
          intro i
          refine Int.ofNat_sub ?_
          omega

        zify [distrib_cast]

    rw [as_int]

    -- Let P be the set of tuples (n, k) where 2 * (k - 1) < n and k * (n - (k - 1)) = 2014
    let P := {(n, k') : ℕ × ℕ+ | 2 * (k' - 1) < n ∧ (k' : ℤ) * ((n : ℤ) - (k' - 1 : ℕ)) = 2014}

    -- then we don't need to consider a sum, just P
    have no_sum : {(n, k') : ℕ × ℕ+ | 2 * (k' - 1) < n ∧ ∑ i : Fin k', ((n : ℤ) - 2 * (i : ℤ)) = 2014 ∧ ∀ i : Fin k', 0 < (n - 2 * i)}
      = P := by
        unfold P
        ext ⟨n, k'⟩
        simp only [Set.mem_setOf_eq, and_congr_right_iff, and_congr_left_iff]
        intro aa

        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, tsub_pos_iff_lt, PNat.pos, Nat.cast_pred]

        rw [←Finset.sum_range (fun x => 2 * (x : ℤ)), ←Finset.mul_sum, ←Nat.cast_sum, mul_sub]
        have two_mul_sum : 2 * (((∑ x ∈ Finset.range ↑k', x) : ℕ) : ℤ)
          = (((∑ x ∈ Finset.range ↑k', x) * 2 : ℕ) : ℤ) := by
            rw [mul_comm _ 2]
            norm_cast
        rw [two_mul_sum, Finset.sum_range_id_mul_two]
        push_cast
        simp only [PNat.pos, Nat.cast_pred, and_iff_left_iff_imp]
        intro bb i
        omega

    rw [no_sum]

    -- divisors of 2014 are positive
    have mem_pos : ∀ k : { x // x ∈ Nat.divisors 2014 }, 0 < k.1 := by
      intro ⟨k, kh⟩
      simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
        gt_iff_lt] at kh ⊢
      apply Nat.pos_of_dvd_of_pos kh
      omega

    -- Let's consider a set S of tuples similar to P, but clearly a finset
    let S : Finset (ℕ × ℕ+)
      := (((Nat.divisors 2014).attach.image (fun k => ⟨k, mem_pos k⟩)
        ).image (fun k : ℕ+ => ⟨(2014 / k) + (k - 1), k⟩)
        ).filter (fun (n, k) => k * (n - (k - 1)) = 2014)

    -- divisors of 2014 are {1, 2, 19, 38, 53, 106, 1007, 2014}, all positive
    have divisors_eq : ((Nat.divisors 2014).attach.image (fun k => ⟨k, mem_pos k⟩)) = ({1, 2, 19, 38, 53, 106, 1007, 2014} : Finset ℕ+) := by decide +revert

    -- so then S is {(2014, 1), (1008, 2), (124, 19), (90, 38), (90, 53), (124, 106), (1008, 1007), (2014, 2014)}
    have S_eq : S = {(2014, 1), (1008, 2), (124, 19), (90, 38), (90, 53), (124, 106), (1008, 1007), (2014, 2014)} := by
      unfold S
      rw [divisors_eq]
      decide

    -- P is a subset of S
    have P_sub : P ⊆ S := by
      intro ⟨n, k⟩
      unfold P S
      simp only [PNat.pos, Nat.cast_pred, tsub_pos_iff_lt, Set.mem_setOf_eq, Finset.coe_filter,
        Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Nat.mem_divisors, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, and_true, and_imp]
      intro aa bb
      have k_pos : 1 ≤ PNat.val k := NeZero.one_le
      split_ands
      · exists k
        have kz_dvd : (k.1 : ℤ) ∣ 2014 := by
          rw [←bb]
          exact Int.dvd_mul_right _ _
        have k_dvd : k.1 ∣ 2014 := Int.ofNat_dvd.mp kz_dvd
        split_ands
        · exists k.1, k_dvd
        · simp only [Prod.mk.injEq, and_true]
          zify [k_pos]
          have div_of_mul := Int.eq_ediv_of_mul_eq_right ?_ bb
          omega
          omega
      · have le_n : (k - 1) ≤ n := by
          have lee : (k - 1) - 1 < n := by
            refine lt_of_le_of_lt ?_ aa
            omega
          exact Nat.le_of_pred_lt lee
        zify [le_n, k_pos]
        exact bb

    -- S is finite, because it's a finset
    have S_finite : S.toSet.Finite := S.finite_toSet

    -- P is finite, because it's a subset of S
    have P_finite : P.Finite := S_finite.subset P_sub

    -- that means P is a fintype
    have : Fintype P := P_finite.fintype

    -- so P can be seen as a finset
    have P_eq : P = P.toFinset.toSet := (Set.coe_toFinset P).symm

    -- P as a finset is a subset of S
    have fin_sub : P.toFinset ⊆ S := Set.toFinset_subset.mpr P_sub

    -- consider the least value of n as a member of P the finset
    suffices hh : IsLeast (P.toFinset.image Prod.fst) 90
    · convert hh
      simp only [Finset.coe_image, Set.coe_toFinset]

    -- We can get the values of P by removing values from S
    have P_eq : P.toFinset = S.filter (fun x => x ∈ P.toFinset) := by
      ext x
      simp only [Finset.mem_filter, iff_and_self]
      exact fun a => fin_sub a

    -- By examining the possible tuples, we see that P only contains (2014, 1), (1008, 2), (124, 19) and (90, 38)
    have P_finset_eq : P.toFinset = {(2014, 1), (1008, 2), (124, 19), (90, 38)} := by
      rw [P_eq, S_eq]
      unfold P
      simp only [PNat.pos, Nat.cast_pred, Set.mem_toFinset, Set.mem_setOf_eq]
      decide

    -- so n is 2014, 1008, 124 or 90
    rw [P_finset_eq]
    simp only [Finset.image_insert, Finset.image_singleton, Finset.coe_insert, Finset.coe_singleton]

    -- and 90 is least
    unfold IsLeast
    norm_num