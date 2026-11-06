import Mathlib

/- 27th Putnam 1966 Problem B2 Prove that at least one integer in any set of ten consecutive integers is relatively prime to the others in the set. -/
theorem number_theory_138672 (n : ℤ)
  : ∃ m ∈ Finset.Icc n (n + 9), ∀ k ∈ Finset.Icc n (n + 9), m ≠ k → IsCoprime m k := by

    -- We can consider the consecutive integers as an explicit set of 10 integers
    have f_eq : Finset.Icc n (n + 9) = {n + 9, n + 8, n + 7, n + 6, n + 5, n + 4, n + 3, n + 2, n + 1, n} := by
      have eqq : n + 9 + 1 - n = 10 := by omega
      rw [Int.Icc_eq_finset_map, eqq]
      simp only [Int.reduceToNat, Finset.range_succ, Finset.range_zero, insert_emptyc_eq, Finset.map_insert,
        Function.Embedding.trans_apply, Nat.castEmbedding_apply, Nat.cast_ofNat,
        addLeftEmbedding_apply, Nat.cast_one, Finset.map_singleton, CharP.cast_eq_zero, add_zero]

    -- The odd numbers can be represented as 5 numbers
    have odds_eq : ∃ k, ((Finset.Icc n (n + 9)).filter Odd) = {k + 8, k + 6, k + 4, k + 2, k} := by
      rw [f_eq]
      obtain ⟨k', kh'⟩ := Int.even_or_odd' n
      rw [@Finset.filter_congr ℤ Odd (fun x => x % 2 = 1) _ _ _ (fun x xh => @Int.odd_iff x)]
      iterate 9 rw [Finset.filter_insert]
      rw [Finset.filter_singleton]
      cases' kh' with h1 h2
      · refine ⟨2 * k' + 1, ?_⟩
        rw [h1]
        iterate 9 rw [←Int.emod_add_emod (2 * k')]
        simp only [Int.mul_emod_right, zero_add, Int.reduceMod, ↓reduceIte, zero_ne_one,
          EuclideanDomain.mod_self, Int.one_emod_two, insert_emptyc_eq]
        iterate 4 rw [add_assoc]
        simp only [Int.reduceAdd]
      · refine ⟨2 * k' + 1, ?_⟩
        rw [h2]
        iterate 9 rw [←Int.emod_add_emod (2 * k' + 1)]
        have eqq : (2 * k' + 1) % 2 = 1 := by omega
        simp only [eqq, Int.reduceAdd, Int.reduceMod, zero_ne_one, ↓reduceIte,
          EuclideanDomain.mod_self]

    -- So the cardinality is 5
    have odds_card : ((Finset.Icc n (n + 9)).filter Odd).card = 5 := by
      obtain ⟨ko, koh⟩ := odds_eq
      rw [koh]
      simp only [Finset.mem_insert, add_right_inj, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff,
        Finset.mem_singleton, add_right_eq_self, OfNat.ofNat_ne_zero, or_self, not_false_eq_true,
        Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd]

    -- Consider the odd integers that are divisible by 3, 5, 7 or neither
    have odd_split : ((Finset.Icc n (n + 9)).filter Odd)
      = ((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 3 ∣ x)
      ∪ ((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 5 ∣ x)
      ∪ ((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 7 ∣ x)
      ∪ ((Finset.Icc n (n + 9)).filter Odd).filter (fun x => ¬(3 ∣ x) ∧ ¬(5 ∣ x) ∧ ¬(7 ∣ x)) := by
        ext aa
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.union_assoc, Finset.mem_union]
        tauto

    -- At most two values are divisible by 3
    have card_3 : (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 3 ∣ x)).card ≤ 2 := by
      obtain ⟨ko, koh⟩ := odds_eq
      rw [koh]

      rw [@Finset.filter_congr ℤ (fun x => 3 ∣ x) (fun x => x % 3 = 0) _ _ _ (fun x xh => @Int.dvd_iff_emod_eq_zero 3 x)]
      iterate 4 rw [Finset.filter_insert]
      rw [Finset.filter_singleton]
      iterate 4 rw [←Int.emod_add_emod ko]

      have : ko % 3 < 3 := Int.emod_lt ko (by tauto)
      have : 0 ≤ ko % 3 := Int.emod_nonneg ko (by tauto)
      interval_cases ko % 3
      simp only [zero_add, Int.reduceMod, OfNat.ofNat_ne_zero, ↓reduceIte, one_ne_zero,
        Finset.mem_singleton, add_right_eq_self, not_false_eq_true, Finset.card_insert_of_not_mem,
        Finset.card_singleton, Nat.reduceAdd, le_refl]
      simp only [Int.reduceAdd, Int.reduceMod, ↓reduceIte, one_ne_zero, OfNat.ofNat_ne_zero,
        EuclideanDomain.mod_self, insert_emptyc_eq, Finset.mem_singleton, add_right_inj,
        OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, not_false_eq_true, Finset.card_insert_of_not_mem,
        Finset.card_singleton, Nat.reduceAdd, le_refl]
      simp only [Int.reduceAdd, Int.reduceMod, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero,
        insert_emptyc_eq, Finset.card_singleton, Nat.one_le_ofNat]

    -- At most one value is divisible by 5
    have card_5 : (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 5 ∣ x)).card ≤ 1 := by
      obtain ⟨ko, koh⟩ := odds_eq
      rw [koh]

      rw [@Finset.filter_congr ℤ (fun x => 5 ∣ x) (fun x => x % 5 = 0) _ _ _ (fun x xh => @Int.dvd_iff_emod_eq_zero 5 x)]
      iterate 4 rw [Finset.filter_insert]
      rw [Finset.filter_singleton]
      iterate 4 rw [←Int.emod_add_emod ko]

      have : ko % 5 < 5 := Int.emod_lt ko (by tauto)
      have : 0 ≤ ko % 5 := Int.emod_nonneg ko (by tauto)
      interval_cases ko % 5
      all_goals
      · simp only [Int.reduceAdd, Int.reduceMod, OfNat.ofNat_ne_zero, one_ne_zero,
          Finset.card_empty, zero_le, ↓reduceIte,
          EuclideanDomain.mod_self, insert_emptyc_eq, Finset.card_singleton, le_refl]

    -- At most one value is divisible by 7
    have card_7 : (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 7 ∣ x)).card ≤ 1 := by
      obtain ⟨ko, koh⟩ := odds_eq
      rw [koh]

      rw [@Finset.filter_congr ℤ (fun x => 7 ∣ x) (fun x => x % 7 = 0) _ _ _ (fun x xh => @Int.dvd_iff_emod_eq_zero 7 x)]
      iterate 4 rw [Finset.filter_insert]
      rw [Finset.filter_singleton]
      iterate 4 rw [←Int.emod_add_emod ko]

      have : ko % 7 < 7 := Int.emod_lt ko (by tauto)
      have : 0 ≤ ko % 7 := Int.emod_nonneg ko (by tauto)
      interval_cases ko % 7
      all_goals
      · simp only [Int.reduceAdd, Int.reduceMod, OfNat.ofNat_ne_zero, one_ne_zero,
          Finset.card_empty, zero_le, ↓reduceIte,
          EuclideanDomain.mod_self, insert_emptyc_eq, Finset.card_singleton, le_refl]

    -- So we have one value which isn't divisible by either
    have k_card : 1 ≤ (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => ¬(3 ∣ x) ∧ ¬(5 ∣ x) ∧ ¬(7 ∣ x))).card := by
      rw [odd_split] at odds_card
      have yep : 5 ≤ (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 3 ∣ x)).card
        + (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 5 ∣ x)).card
        + (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => 7 ∣ x)).card
        + (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => ¬(3 ∣ x) ∧ ¬(5 ∣ x) ∧ ¬(7 ∣ x))).card := by
          rw [←odds_card]
          refine le_trans (Finset.card_union_le _ _) ?_
          refine Nat.add_le_add ?_ (le_refl _)
          refine le_trans (Finset.card_union_le _ _) ?_
          refine Nat.add_le_add ?_ (le_refl _)
          exact Finset.card_union_le _ _
      linarith

    -- let k be such an element
    obtain ⟨k, kh⟩ : (((Finset.Icc n (n + 9)).filter Odd).filter (fun x => ¬(3 ∣ x) ∧ ¬(5 ∣ x) ∧ ¬(7 ∣ x))).Nonempty
      := Finset.card_pos.mp k_card

    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_filter] at kh
      exact kh.1.1

    -- let m ≠ k be a different element, which we'll prove has to be coprime
    -- i.e. that k.gcd m = 1
    intro m mh hh
    clear odd_split f_eq odds_card odds_eq k_card card_3 card_5 card_7

    simp only [Finset.mem_filter] at kh
    have k_dvd' : (k.gcd m : ℤ) ∣ k
      := Int.ofNat_dvd_left.mpr <| Nat.gcd_dvd_left k.natAbs m.natAbs
    have m_dvd' : (k.gcd m : ℤ) ∣ m
      := Int.ofNat_dvd_left.mpr <| Nat.gcd_dvd_right k.natAbs m.natAbs

    -- 2 does not divide k, because it's odd
    have k_odd : ¬((2 : ℤ) ∣ k) := by
      by_contra ho
      exact absurd kh.1.2 <| Int.not_odd_iff_even.mpr <| even_iff_two_dvd.mpr ho

    -- We have that 0 ≤ k.gcd m ≤ 9
    have : k.gcd m ≤ 9 := by
      refine Int.ofNat_le.mp ?_
      by_cases hkm : m < k
      · refine le_trans (Int.le_of_dvd (by omega) <| Int.dvd_sub k_dvd' m_dvd') ?_
        simp only [Finset.mem_Icc] at mh kh
        omega
      · refine le_trans (Int.le_of_dvd (by omega) <| Int.dvd_sub m_dvd' k_dvd') ?_
        simp only [Finset.mem_Icc] at mh kh
        omega
    have : 0 ≤ k.gcd m := by positivity

    -- But the only case that works is k.gcd m = 1
    interval_cases hhh : k.gcd m
    · simp only [CharP.cast_eq_zero, zero_dvd_iff] at k_dvd' m_dvd'
      have zero_lt_zero := k_dvd' ▸ (m_dvd' ▸ hh)
      contradiction
    · exact Int.isCoprime_iff_gcd_eq_one.mpr hhh
    · rw [Nat.cast_ofNat] at k_dvd'
      exact absurd k_dvd' k_odd
    · rw [Nat.cast_ofNat] at k_dvd'
      exact absurd k_dvd' kh.2.1
    · rw [Nat.cast_ofNat] at k_dvd'
      exact absurd (dvd_trans (by decide) k_dvd') k_odd
    · rw [Nat.cast_ofNat] at k_dvd'
      exact absurd k_dvd' kh.2.2.1
    · rw [Nat.cast_ofNat] at k_dvd'
      exact absurd (dvd_trans (by decide) k_dvd') k_odd
    · rw [Nat.cast_ofNat] at k_dvd'
      exact absurd k_dvd' kh.2.2.2
    · rw [Nat.cast_ofNat] at k_dvd'
      exact absurd (dvd_trans (by decide) k_dvd') k_odd
    · have km_eq_zero : k - m = 0 := eq_zero_of_neg_eq (by omega)
      have k_eq_m : k = m := Int.eq_of_sub_eq_zero km_eq_zero
      contradiction