import Mathlib

/-- How many of the integers between 1 and 1000, inclusive,
  can be expressed as the difference of the squares of two nonnegative integers? -/
theorem number_theory_96717 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 1000 ∧ ∃ m n, x = m^2 - n^2} = 750 := by
  -- we show that exactly numbers equivalent to 2 mod 4 can not be obtained.
  have condition x : (∃ m n, x = m^2 - n^2) ↔ ¬ x ≡ 2 [MOD 4] := by
    mod_cases xmod : x % 4
    -- If x=4b is divisible by 4, consider (b+1)^2 - (b-1)^2 = 4b = x.
    · apply iff_of_true
      · rw[Nat.modEq_zero_iff_dvd] at xmod
        obtain ⟨m,rfl⟩ := xmod
        cases m with
        | zero => exists 0; exists 0
        | succ m => exists (m + 2); exists m; apply Nat.eq_sub_of_add_eq; ring
      · intro xmod'
        unfold Nat.ModEq at *
        rw[xmod'] at xmod
        have := Nat.mod_injOn_Ico 0 4 (by simp) (by simp) xmod
        simp at this
    -- If x=4b+1, consider (2b+1)^2 - (2b)^2
    · apply iff_of_true
      · have : 1 ≤ x := Nat.ModEq.le_of_lt_add xmod.symm (by simp)
        symm at xmod
        rw[Nat.modEq_iff_dvd' this] at xmod
        obtain ⟨m,eq⟩ := xmod
        rw[Nat.sub_eq_iff_eq_add this] at eq
        rw[eq]
        exists (2 * m + 1)
        use (2 * m)
        ring_nf
        rw[Nat.add_sub_cancel_right]
      · intro xmod'
        unfold Nat.ModEq at *
        rw[xmod'] at xmod
        have := Nat.mod_injOn_Ico 0 4 (by simp) (by simp) xmod
        simp at this
    -- If x = 4b+2, it cannot be obtained, since squares are 0,1 mod 4.
    · apply iff_of_false
      · push_neg
        rintro m n eq
        have le : n^2 ≤ m^2 := by
          have : x ≠ 0 := by
            rintro rfl
            contradiction
          apply le_of_lt
          apply Nat.lt_of_sub_ne_zero
          rwa[eq] at this
        rcases eq
        rw[← ZMod.eq_iff_modEq_nat, Nat.cast_sub le, Nat.cast_pow, Nat.cast_pow] at xmod
        generalize (m : ZMod 4) = m', (n : ZMod 4) = n' at xmod
        fin_cases m' <;> fin_cases n' <;> contradiction
      · rwa[not_not]
    -- If x = 4b+3, consider (2b+2)^2 - (2b+1)^2
    · apply iff_of_true
      · have : 3 ≤ x := Nat.ModEq.le_of_lt_add xmod.symm (by simp)
        symm at xmod
        rw[Nat.modEq_iff_dvd' this] at xmod
        obtain ⟨m,eq⟩ := xmod
        rw[Nat.sub_eq_iff_eq_add this] at eq
        rw[eq]
        exists (2 * m + 2)
        use (2 * m + 1)
        ring_nf
        omega
      · intro xmod'
        unfold Nat.ModEq at *
        rw[xmod'] at xmod
        have := Nat.mod_injOn_Ico 0 4 (by simp) (by simp) xmod
        simp at this
  -- It remains to show that there are 750 numbers <= 1000, >= 1 that are not 2 mod 4.
  conv => lhs; rhs; intro n; lhs; intro x; rw[condition]
  convert_to Set.ncard ({x : ℕ | x < 1001 ∧ ¬ x ≡ 2 [MOD 4]} \ {0}) = 750 using 2
  · ext a
    cases a with
    | zero => simp
    | succ n => simp[Nat.lt_succ]
  -- We know that there are 751 ones including 0,
  · have := Nat.count_modEq_card_eq_ceil 1001 (r := 4) (by simp) 2
    rw[Nat.count_eq_card_filter_range] at this
    rw[← Set.ncard_coe_Finset] at this
    simp at this
    have eq : ({x | x < 1001 ∧ ¬x ≡ 2 [MOD 4]} \ {0}) = (Set.Iio 1001 \ {x | x < 1001 ∧ x ≡ 2 [MOD 4]}) \ {0} := by
      congr 1; ext a; simpa using Or.inl
    rw[eq]
    -- and by difference forming, there must be 250 remaining.
    have sub := Nat.eq_sub_of_add_eq $ Set.ncard_diff_add_ncard_of_subset (by intro a ha; exact ha.1) (s := {x | x < 1001 ∧ x ≡ 2 [MOD 4]}) (t := Set.Iio 1001)
      (ht := Set.finite_Iio _)
    rw[Set.ncard_diff ?zero,sub, Set.ncard_eq_toFinset_card (hs := Set.finite_Iio 1001)]
    simp only [Set.toFinite_toFinset, Set.toFinset_Iio, Nat.card_Iio, Set.ncard_singleton,
      Nat.pred_eq_succ_iff, Nat.reduceAdd]
    suffices h : {x | x < 1001 ∧ x ≡ 2 [MOD 4]}.ncard = 250 by rw[h]
    norm_num at this
    apply (Nat.cast_inj (R := ℤ)).mp
    rw[this]
    rfl
    case zero =>
      simp only [Set.singleton_subset_iff, Set.mem_diff, Set.mem_Iio, Nat.ofNat_pos,
        Set.mem_setOf_eq, true_and]
      intro h
      contradiction