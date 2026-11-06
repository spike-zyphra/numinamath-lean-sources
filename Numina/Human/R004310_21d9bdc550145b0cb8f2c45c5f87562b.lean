import Mathlib


/- What is the maximum number of integers we can choose from the set $\{1,2,3, \ldots, 2017\}$ such that the difference between any two of them is not a prime number? -/
theorem number_theory_251637 : IsGreatest {n : ℕ |
  ∃ s : Finset ℕ, s ⊆ (Finset.Icc 1 2017) ∧ s.card = n ∧ ∀ m ∈ s, ∀ n ∈ s, m ≠ n → ¬Nat.Prime (m - n)} 505 := by

  rw [IsGreatest, upperBounds]
  simp only [ne_eq, Set.mem_setOf_eq, forall_exists_index, and_imp]
  constructor

  · -- 1,5,9,...,2013,2017 satisfy the condition.
    -- since each is of the form 4k+1, their difference 4k is not prime
    -- and this set has 505 numbers in total.
    set f: ℕ → ℕ := fun k => 4*k+1 with f_def
    set s := (Finset.image f (Finset.range 505)) with s_def
    use s
    split_ands
    · simp only [s_def, f_def]
      native_decide
    · rw [show 505 = (Finset.range 505).card by simp]
      symm
      refine Finset.card_nbij f ?_ ?_ ?_
      · simp [f_def, s_def]
      · intro x1 hx1 x2 hx2 hx1x2
        simp only [f_def, Nat.add_right_cancel_iff, mul_eq_mul_left_iff,
        OfNat.ofNat_ne_zero, or_false] at hx1x2
        exact hx1x2
      · intro y hy
        simp only [s_def, Finset.coe_image, Finset.coe_range,
        Set.mem_image, Set.mem_Iio] at hy
        rcases hy with ⟨x, hx, hxy⟩
        use x
        simp [hx, hxy]
    · intro m hm n hn hmn
      simp only [s_def, Finset.mem_image, Finset.mem_range] at hm hn
      rcases hm with ⟨a, ha, rfl⟩
      rcases hn with ⟨b, hb, rfl⟩
      have: f a - f b = 4 * (a - b) := by
        simp [f_def, Nat.mul_sub]
      rw [this]
      rw [Nat.prime_mul_iff]
      simp only [OfNat.ofNat_ne_one, and_false, or_false, not_and]
      norm_num

  · rintro _ s hs rfl h
    -- take 2017 out.
    have h1: Finset.Icc 1 2017 = insert 2017 (Finset.Icc 1 2016) := by
      native_decide
    -- cut 1 to 2016 into 252 intervals, each interval has length 8.
    set t: ℕ → Finset ℕ :=
      fun n => Finset.filter (· ∈ s) (Finset.Icc (8*n+1) (8*n+8)) with t_def
    have h2: s.erase 2017 = Finset.biUnion (Finset.range 252) t := by
      ext x
      simp only [Finset.mem_erase, ne_eq, t_def,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hx1, hx2⟩
        specialize hs hx2
        simp only [Finset.mem_Icc] at hs
        simp only [hx2, and_true]
        clear * - hx1 hs
        rcases hs with ⟨xge, xle⟩
        replace xle: x ≤ 2016 := by omega
        clear hx1
        native_decide +revert
      · rintro ⟨a, alt, hx, x_mem⟩
        simp only [x_mem, and_true]
        apply ne_of_lt
        apply lt_of_le_of_lt hx.right ?_
        linarith only [alt]
    -- and we find from each 8 consecutive numbers, if difference of any two numbers is no prime,
    -- at most two numbers can be choosen.
    -- this is because for {n,n+1,n+2,...,n+8}, if n is choosen, then n+2,n+3,n+5,n+7 cannot be choosen.
    -- and n+1,n+6, n+1,n+4, n+4,n+6 cannot both be choosen, since their difference 5,3,2 is prime.
    -- so at most two numbers. and if we skip n, choose from n+1, same argument works on n+1 to n+9.
    have h3: ∀ss ⊆ (Finset.range 8),
      (∀ x1 ∈ ss, ∀ x2 ∈ ss, ¬ Nat.Prime (x1 - x2)) → ss.card ≤ 2 := by
      native_decide
    have h4: ∀i ∈ Finset.range 252, (t i).card ≤ 2 := by
      intro i hi
      by_contra!
      set s2 := (Finset.filter (· + (8*i+1) ∈ s) (Finset.range 8)) with s2_def
      have hs21: s2 ⊆ Finset.range 8 := by
        rw [s2_def]
        simp only [Finset.filter_subset]
      have hs22: ∀ x1 ∈ s2, ∀ x2 ∈ s2, ¬ Nat.Prime (x1 - x2) := by
        intro x1 hx1 x2 hx2
        simp only [s2_def, Finset.mem_filter, Finset.mem_range] at hx1 hx2
        specialize h (x1 + (8*i+1)) hx1.right (x2 + (8*i+1)) hx2.right
        by_cases hh: x1 + (8*i+1) = x2 + (8*i+1)
        · simp only [Nat.add_right_cancel_iff] at hh
          norm_num [hh]
        · specialize h hh
          rwa [show (x1 + (8*i+1)) - (x2 + (8*i+1)) = x1 - x2 by omega] at h
      specialize h3 s2 hs21 hs22
      have h4: (t i).card = s2.card := by
        simp only [s2_def, t_def]
        symm
        refine Finset.card_nbij (fun n => n + (8*i+1)) ?_ ?_ ?_
        · intro x
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
          le_add_iff_nonneg_left, zero_le, true_and, and_imp]
          intro xlt hx
          constructor
          · linarith only [xlt]
          · exact hx
        · intro _ _ _ _
          simp only [Nat.add_right_cancel_iff, imp_self]
        · intro y hy
          simp only [Finset.coe_filter, Finset.mem_range,
          Set.mem_image, Set.mem_setOf_eq] at hy ⊢
          use (y - (8*i+1))
          simp only [Finset.mem_Icc] at hy
          simp only [hy.left.left, Nat.sub_add_cancel, hy.right, and_true]
          have := hy.left.right
          clear * - this
          omega
      rw [h4] at this
      absurd h3
      push_neg
      exact this
    -- then card of numbers from s between 1,2016 is at most 504.
    -- and therefore card of s ≤ 505
    have h5: (s.erase 2017).card ≤ 504 := by
      rw [show 504 = (Finset.range 252).card * 2 by simp, h2]
      apply Finset.card_biUnion_le_card_mul _ _ _ h4
    by_cases hh: 2017 ∈ s
    · rw [Finset.card_erase_of_mem hh] at h5
      omega
    · rw [Finset.card_erase_eq_ite, if_neg hh] at h5
      exact h5.trans (by norm_num)