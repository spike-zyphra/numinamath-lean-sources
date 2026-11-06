import Mathlib

/- 9. The numbers $1,2, \ldots, 2016$ were divided into pairs, such that the product of the numbers in each pair does not exceed some natural number $N$. What is the smallest $N$ for which this is possible? -/
theorem number_theory_191315 :
  IsLeast {N | ∃ f : Finset.Icc 1 2016 ≃ Finset.Icc 1 2016, ∀ s ∈ (Finset.Icc 1 2016).attach, s.1 * (f s).1 ≤ N ∧ s ≠ f s ∧ f (f s) = s} 1017072
  := by
    constructor
    -- We achieve the minimum 1017072 = 1008*1009 with the pairs (1, 2016), (2, 2015), ...(1008, 1009)
    · simp only [id_eq, Set.mem_setOf_eq]
      refine ⟨?_, ?_⟩

      -- our pairing function is f(x) = 2017 - x
      · let f : { x // x ∈ Finset.Icc 1 2016 } → { x // x ∈ Finset.Icc 1 2016 } := by
          intro ⟨aa, bb⟩
          refine ⟨2017 - aa, ?_⟩
          simp only [Finset.mem_Icc, tsub_le_iff_right] at bb ⊢
          omega

        -- f is involutive
        have f_inv : Function.Involutive f := by
          intro ⟨xx1, xx2⟩
          unfold f
          simp only [eq_mp_eq_cast, id_eq, Nat.cast_ofNat, Int.reduceNeg, Int.Nat.cast_ofNat_Int,
            Int.reduceAdd, eq_mpr_eq_cast]
          refine Subtype.eq ?_
          simp only
          refine Nat.sub_sub_self ?_
          simp only [Finset.mem_Icc] at xx2
          exact Nat.le_succ_of_le xx2.2

        -- so it's a bijection
        exact Equiv.ofBijective f f_inv.bijective
      · simp only [Finset.mem_attach, Equiv.ofBijective_apply, ne_eq, forall_const, Subtype.forall,
          Finset.mem_Icc, Subtype.mk.injEq, and_imp]
        intro n aa bb
        refine ⟨?_, ?_⟩
        -- the product of pairs has 1008*1009 as a maximum
        · convert_to n * (2017 - n) ≤ 1008*1009
          -- n * (2017 - n) is "symmetric", so we just consider n ≤ 1008
          wlog split : n ≤ 1008 generalizing n
          · have flipped := this (2017 - n) (by omega) (by omega) (by omega)
            convert flipped using 1
            rw [mul_comm]
            congr
            omega
          clear bb
          -- Consider the equation over the reals
          convert_to (n : ℝ) * (2017 - (n : ℝ)) ≤ 1008 * 1009
          · have : n ≤ 2017 := by linarith
            norm_cast
          -- then if we examine when n ≤ 1008, we see that it's less than 1008*1009
          have : (n : ℝ) ≤ 1008 := by norm_cast
          nlinarith
        · omega
    -- now we'll show that 1017072 = 1008*1009 is a lower bound
    · rw [mem_lowerBounds]
      simp only [Finset.mem_attach, ne_eq, forall_const, Subtype.forall,
        Set.mem_setOf_eq, forall_exists_index]
      intro x f ha

      -- there must be some value above 1008 which is paired with another value above 1008
      obtain ⟨k, kh1, kh2⟩ : ∃ a, 1008 ≤ a.1 ∧ 1008 ≤ (f a).1 := by
        -- assume the oppositve
        by_contra cont
        simp only [Subtype.exists, exists_and_left, not_exists, not_and,
          not_le] at cont

        -- Then consider all values larger than or equal to 1008, S
        let S : Finset { x // x ∈ Finset.Icc 1 2016 }
          := Finset.subtype (fun x => x ∈ Finset.Icc 1 2016) (Finset.Icc 1008 2016 : Finset ℕ)

        -- and all values less than 1008, T
        let T : Finset { x // x ∈ Finset.Icc 1 2016 }
          := Finset.subtype (fun x => x ∈ Finset.Icc 1 2016) (Finset.Icc 1 1007 : Finset ℕ)
        -- S is larger than T
        have cards : T.card * 1 < S.card := by
          rw [mul_one]
          unfold S T
          simp only [Finset.card_subtype]
          rw [Finset.filter_true_of_mem, Finset.filter_true_of_mem]
          simp only [Nat.card_Icc, Nat.reduceAdd, Nat.add_one_sub_one, Nat.reduceSub, Nat.reduceLT]
          apply Finset.Icc_subset_Icc <;> decide
          apply Finset.Icc_subset_Icc <;> decide

        -- but by assuming the opposite we have that every value in S is mapped to T
        have mems : ∀ a ∈ S, f a ∈ T := by
          unfold S T
          intro aa bb
          rw [Finset.mem_subtype]
          rw [Finset.mem_subtype] at bb
          have aa_mem_above : aa.1 ∈ Finset.Icc 1 2016 := by
            apply Finset.Icc_subset_Icc ?_ ?_ bb
            decide
            decide
          rw [Finset.mem_Icc] at bb
          have faa_lt := cont aa.1 bb.1 aa_mem_above
          rw [Finset.mem_Icc]
          refine ⟨?_, ?_⟩
          · exact (Finset.mem_Icc.mp (f aa).2).1
          · simp only [Subtype.coe_eta] at faa_lt
            exact Nat.le_of_lt_succ faa_lt


        -- which by the pigeonhole principle means there's at least two values
        -- in S which map to the same value in T using f
        obtain ⟨k, kh1, kh2⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to mems cards
        obtain ⟨aa, ah, bb, bh, hh⟩ := Finset.one_lt_card.mp kh2
        simp only [Finset.mem_filter] at ah bh
        have gg1 := ah.2
        have gg2 := bh.2

        -- but f is injective, contradiction
        rw [←gg2] at gg1
        exact hh <| f.injective gg1

      -- we use the properties of f
      have f_props := ha k k.2

      -- ...and that no value is paired with themselves
      have f_ne : (f k).1 ≠ k.1 := by
        refine Subtype.coe_ne_coe.mpr ?_
        have yee := f_props.2.1
        simp only [Subtype.coe_eta] at yee
        simp only [ne_eq]
        exact fun a => yee a.symm

      -- ...to show the bound
      convert_to 1008*1009 ≤ x
      by_cases hk : k.1 = 1008
      · rw [hk] at f_ne
        have lt_fk : 1008 < (f k).1 := Nat.lt_of_le_of_ne kh2 f_ne.symm
        refine le_trans ?_ f_props.1
        refine mul_le_mul kh1 lt_fk ?_ ?_
        exact Nat.zero_le 1009
        exact Nat.zero_le k.1
      · rw [mul_comm]
        have lt_k : 1008 < k.1 := Nat.lt_of_le_of_ne kh1 fun a => hk a.symm
        refine le_trans ?_ f_props.1
        refine mul_le_mul lt_k kh2 ?_ ?_
        exact Nat.zero_le 1008
        exact Nat.zero_le k.1