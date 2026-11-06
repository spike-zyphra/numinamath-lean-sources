import Mathlib

/- Find the sum of all positive integers $n$ such that, given an unlimited supply of stamps of denominations $5,n,$ and $n+1$ cents, $91$ cents is the greatest postage that cannot be formed. -/
theorem number_theory_97938
: (∑' (x : {n : ℕ | 0 < n ∧ FrobeniusNumber 91 {5, n, n+1}}), (x : ℕ)) = 71 := by
  -- Let `f a n` be true iff `a` is summable using `5`, `n` and `n + 1`.
  let f : ℕ → ℕ → Prop := fun a n => a ∈ AddSubmonoid.closure {5, n, n+1}

  -- `n = 0` is summable to 91
  have f_zero : f 91 0
  · unfold f
    have set_split : ({5, 0, 1} : Set ℕ) = {0} ∪ {5, 1} := Set.insert_comm 5 0 {1}
    rw [set_split, AddSubmonoid.closure_union, AddSubmonoid.closure_singleton_zero]
    simp only [bot_le, sup_of_le_right]
    rw [AddSubmonoid.mem_closure_pair]
    refine ⟨18, 1, ?_⟩
    simp only [smul_eq_mul, Nat.reduceMul, mul_one, Nat.reduceAdd]

  -- We can represent `AddSubmonoid.closure` as a linear combinarions
  have mem_closure_three : ∀ {k x y z : ℕ}, k ∈ AddSubmonoid.closure {x, y, z} ↔ ∃ a b c, a*x + b*y + c*z = k
  · intro k x y z
    have as_range : {x, y, z} = Set.range ![x, y, z]
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
        Set.union_empty, Set.union_singleton, Set.union_insert]
      ext aa
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    rw [as_range, AddSubmonoid.mem_closure_range_iff_of_fintype]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_eq_mul]
    constructor
    · intro hh
      obtain ⟨ff, hh⟩ := hh
      rw [Fin.sum_univ_three] at hh
      refine ⟨ff 0, ff 1, ff 2, ?_⟩
      simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons] using hh.symm
    · intro hh
      obtain ⟨aa, bb, cc, hh⟩ := hh
      refine ⟨![aa, bb, cc], ?_⟩
      rw [Fin.sum_univ_three]
      simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons] using hh.symm

  -- If we have a solution for 96 where b or c is at least 5, then we have a solution for 91
  have five_le_coeff : ∀ n b c, 0 < n → 5 ≤ b ∨ 5 ≤ c → b*n + c*(n+1) = 96 → 91 ∈ AddSubmonoid.closure {5, n, n+1}
  · intro n b c hn ge eqq
    apply mem_closure_three.mpr
    cases' ge with hb hc
    -- When 5 ≤ b
    · let bb := b - (b % 5)
      have dvd_bb : 5 ∣ bb := Nat.dvd_sub_mod b
      obtain ⟨kk, ll⟩ := dvd_iff_exists_eq_mul_left.mp dvd_bb
      suffices h : (n*kk)*5 + (b % 5)*n + c*(n+1) = 96
      · refine ⟨((n * kk) - 1), b % 5, c, ?_⟩
        convert_to ((n * kk) - 1) * 5 + b % 5 * n + c * (n + 1) = 96 - 5
        rw [←h, Nat.sub_mul, mul_assoc, ←ll, one_mul]
        have : 1*5 ≤ n * bb := Nat.mul_le_mul hn (by omega)
        omega
      rw [←eqq]
      congr 1
      nth_rw 3 [mul_comm]
      rw [mul_assoc, ←Nat.mul_add, ←ll]
      rw [mul_comm]
      congr
      exact Nat.sub_add_cancel (Nat.mod_le b 5)
    -- Repeat for 5 ≤ c
    · let cc := c - (c % 5)
      have dvd_cc : 5 ∣ cc := Nat.dvd_sub_mod c
      obtain ⟨kk, ll⟩ := dvd_iff_exists_eq_mul_left.mp dvd_cc
      suffices h : ((n+1)*kk)*5 + b*n + (c % 5)*(n+1) = 96
      · refine ⟨(((n+1)*kk)-1), b, c % 5, ?_⟩
        convert_to (((n + 1) * kk) - 1) * 5 + b * n + (c % 5) * (n + 1) = 96 - 5
        rw [←h, Nat.sub_mul, mul_assoc, ←ll, one_mul]
        have : 1*5 ≤ (n + 1) * cc := Nat.mul_le_mul (by omega) (by omega)
        omega
      rw [←eqq]
      rw [mul_assoc, ←ll]
      unfold cc
      rw [add_assoc]
      nth_rw 3 [add_comm]
      nth_rw 5 [add_comm]
      rw [←add_assoc]
      congr 1
      rw [mul_comm, ←add_mul]
      congr
      exact Nat.sub_add_cancel (Nat.mod_le c 5)

  -- We'll show that the only valid numbers are 24 and 47
  suffices sols : {n | 0 < n ∧ FrobeniusNumber 91 {5, n, n + 1}} = ({24, 47} : Finset ℕ).toSet
  · rw [sols]
    simp only [Finset.coe_sort_coe]
    convert_to ∑' (x : { x // x ∈ {24, 47} }), id x.val = 71
    rw [Finset.tsum_subtype {24, 47} id]
    decide

  -- We chain set equalities
  calc {n | 0 < n ∧ FrobeniusNumber 91 {5, n, n + 1}}
  -- We can ignore n = 0
  _ = {n | FrobeniusNumber 91 {5, n, n + 1}} := by
    ext nn
    simp only [Set.mem_setOf_eq, and_iff_right_iff_imp]
    intro gg
    by_contra hh
    simp only [not_lt, nonpos_iff_eq_zero] at hh
    refine absurd (hh ▸ gg) ?_
    unfold FrobeniusNumber IsGreatest
    simp only [zero_add, Set.mem_setOf_eq, not_and]
    exact fun aa _ ↦ aa f_zero

  -- To show that the Frobenius Number is 91, we just need to show that 91 is not summable, and that 92-96 is summable
  _ = {n | (¬f 91 n) ∧ (f 92 n) ∧ (f 93 n) ∧ (f 94 n) ∧ (f 95 n) ∧ (f 96 n)} := by
    ext nn
    simp only [Set.mem_setOf_eq]
    unfold FrobeniusNumber IsGreatest f
    rw [Set.mem_setOf_eq, and_congr_right_iff]
    intro hh
    constructor
    -- If 91 is the largest non-reachable, then 92-96 are reachable
    · intro mem_upper
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals
      · by_contra hh
        have := mem_upper hh
        tauto
    -- If 92-96 are reachable then 91 is the largest non-reachable
    · intro ⟨aa, bb, cc, dd, ee⟩
      rw [upperBounds]
      simp only [Set.mem_setOf_eq]
      intro jj kk
      -- Assume that some jj > 91 is non-reachable
      by_contra hh
      -- But jj is reachable, contradiction
      refine absurd kk ?_
      -- We rewrite jj = 92 + b + c, where 5 ∣ b and c < 5
      · obtain ⟨k, kh⟩ := Nat.exists_eq_add_of_le' (not_le.mp hh)
        obtain ⟨k', kh'⟩ : ∃ k', k = 5*k' + (k % 5)
        · refine ⟨(k - (k % 5))/5, ?_⟩
          rw [Nat.mul_div_eq_iff_dvd.mpr (Nat.dvd_sub_mod k)]
          exact (Nat.sub_eq_iff_eq_add (Nat.mod_le k 5)).mp rfl
        rw [kh, kh', Nat.add_right_comm, add_assoc, mul_comm]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, not_not]
        refine AddSubmonoid.add_mem _ ?_ ?_
        · refine AddSubmonoid.nsmul_mem (AddSubmonoid.closure {5, nn, nn + 1}) ?_ k'
          exact AddSubmonoid.subset_closure (Set.mem_insert 5 {nn, nn + 1})
        -- Then we can use a solution for 92-96
        · have : k % 5 < 5 := Nat.mod_lt k (by tauto)
          interval_cases k % 5 <;> assumption

  -- 96 has to be summable with coefficients smaller than 5
  _ = {n | (¬f 91 n) ∧ (f 92 n) ∧ (f 93 n) ∧ (f 94 n) ∧ (f 95 n) ∧ (∃ b c, b < 5 ∧ c < 5 ∧ b * n + c * (n + 1) = 96)} := by
    ext nn
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
    by_cases hue : nn = 0
    · subst hue
      simp only [f_zero, not_true_eq_false, false_and, exists_and_left]

    simp only [exists_and_left, and_congr_right_iff]
    intro aa bb cc dd ee
    constructor
    · intro ff
      obtain ⟨a, b, c, habc⟩ := mem_closure_three.mp ff
      by_cases h : a = 0
      · subst h
        rw [zero_mul, zero_add] at habc
        by_cases hh : b < 5 ∧ c < 5
        · exact ⟨b, hh.1, c, hh.2, habc⟩
        · exact False.elim <| aa <| five_le_coeff nn b c (by omega) (by omega) habc
      · refine absurd ?_ aa
        apply mem_closure_three.mpr
        refine ⟨(a-1), b, c, ?_⟩
        calc (a - 1) * 5 + b * nn + c * (nn + 1)
          _ = a * 5 - 5 + b * nn + c * (nn + 1) := by rw [Nat.sub_mul]
          _ = a * 5 + b * nn - 5 + c * (nn + 1) := by
            rw [Nat.sub_add_comm]
            exact Nat.le_mul_of_pos_left 5 (Nat.zero_lt_of_ne_zero h)
          _ = a * 5 + b * nn + c * (nn + 1) - 5 := by
            rw [←Nat.sub_add_comm]
            refine Nat.le_add_right_of_le ?_
            exact Nat.le_mul_of_pos_left 5 (Nat.zero_lt_of_ne_zero h)
          _ = 91 := by rw [habc]
    · intro ff
      obtain ⟨b, bh, c, ch, bch⟩ := ff
      apply mem_closure_three.mpr
      refine ⟨0, b, c, ?_⟩
      rw [zero_mul, zero_add]
      exact bch

  -- Seperate 96 solutions into seperate set
  _ = {n | (∃ b c, b < 5 ∧ c < 5 ∧ b * n + c * (n + 1) = 96)} ∩ {n | (¬f 91 n) ∧ (f 92 n) ∧ (f 93 n) ∧ (f 94 n) ∧ (f 95 n)} := by
    rw [←Set.setOf_and]
    ext n
    simp only [Set.mem_setOf_eq]
    tauto

  -- Consider solutions of 96 as a finite set of 0 ≤ a, b ≤ 4
  -- where `a * n + b * (n + 1) = 96` with `n` an integer, i.e. `n = (96 - b) / (a + b)`.
  _ = ( Finset.toSet
        <| Finset.image (fun (⟨a, b, n⟩ : ℕ × ℕ × ℕ) => n)
        <| Finset.filter (fun ⟨a, b, n⟩ => a * n + b * (n + 1) = 96)
        <| Finset.image (fun ⟨a, b⟩ => ⟨a, b, (96 - b) / (a + b)⟩)
        <| Finset.Icc 0 4 ×ˢ Finset.Icc 0 4
      ) ∩ {n | (¬f 91 n) ∧ (f 92 n) ∧ (f 93 n) ∧ (f 94 n) ∧ (f 95 n)} := by
    congr
    ext n
    simp only [exists_and_left, Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter,
      Finset.mem_image, Finset.mem_product, Finset.mem_Icc, zero_le, true_and, Prod.exists,
      Set.mem_image, Prod.mk.injEq, exists_eq_right]
    constructor
    · intro ⟨aa, bb, cc, dd, ee⟩
      refine ⟨aa, cc, ⟨⟨aa, cc, ?_⟩, ?_⟩⟩
      · simp only [true_and]
        constructor
        · constructor
          · exact Nat.le_of_lt_succ bb
          · exact Nat.le_of_lt_succ dd
        · interval_cases aa <;> interval_cases cc <;> omega
      · exact ee

    · intro ⟨aa, bb, ⟨cc, dd, ⟨e1, e2⟩, ff, gg, hh⟩, ii⟩
      subst ff
      subst gg
      refine ⟨cc, ?_, dd, ?_, ii⟩ <;> omega

  -- Of those 16 (a, b) pairs, only 9 work
  _ = ({95, 47, 31, 23, 96, 48, 32, 24, 19} : Finset ℕ).toSet
    ∩ {n | (¬f 91 n) ∧ (f 92 n) ∧ (f 93 n) ∧ (f 94 n) ∧ (f 95 n)} := by congr

  -- We check the rest manually and find that only 24 and 47 work
  _ = ({24, 47} : Finset ℕ) := by
    ext n
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_setOf_eq]
    unfold f
    constructor
    · intro ⟨aa, bb⟩
      rcases aa with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
      -- `n = 95` can't sum to 92
      · refine absurd (h1 ▸ bb.2.1) ?_
        rw [mem_closure_three]
        simp only [not_exists]
        intro a b c
        omega
      -- `n = 47` works
      · exact Or.inr h2
      -- `n = 31` can sum to 91
      · exact absurd (mem_closure_three.mpr ⟨12, 1, 0, by decide⟩) <| h3 ▸ bb.1
      -- `n = 23` can sum to 91
      · exact absurd (mem_closure_three.mpr ⟨9, 2, 0, by decide⟩) <| h4 ▸ bb.1
      -- `n = 96` can't sum to 92
      · refine absurd (h5 ▸ bb.2.1) ?_

        rw [mem_closure_three]
        simp only [not_exists]
        intro a b c
        by_cases b ≠ 0 <;> omega
      -- `n = 48` can't sum to 92
      · refine absurd (h6 ▸ bb.2.1) ?_
        rw [mem_closure_three]
        simp only [not_exists]
        intro a b c
        by_cases hb : 2 ≤ b
        · omega
        · by_cases hc : 2 ≤ c
          · omega
          · rw [not_le] at hb hc
            interval_cases b <;> interval_cases c <;> omega
      -- `n = 32` can sum to 91
      · exact absurd (mem_closure_three.mpr ⟨5, 0, 2, by decide⟩) <| h7 ▸ bb.1
      -- `n = 24` works
      · exact Or.inl h8
      -- `n = 19` can sum to 91
      · exact absurd (mem_closure_three.mpr ⟨3, 4, 0, by decide⟩) <| h9 ▸ bb.1
    -- Then we show that `n = 24` and `n = 47` works
    · intro aa
      rcases aa with h1 | h2
      -- `n = 24` first
      · subst h1
        simp only [Nat.reduceEqDiff, Nat.succ_ne_self, or_false, or_true, true_and]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        -- can't sum to 91
        · simp only [mem_closure_three, not_exists]
          intro a b c
          by_cases hb : b ≤ 3
          by_cases hc : c ≤ 3
          · interval_cases b <;> interval_cases c <;> omega
          · omega
          · omega
        -- can sum to 92
        · exact mem_closure_three.mpr ⟨4, 3, 0, by decide⟩
        -- can sum to 93
        · exact mem_closure_three.mpr ⟨9, 2, 0, by decide⟩
        -- can sum to 94
        · exact mem_closure_three.mpr ⟨14, 1, 0, by decide⟩
        -- can sum to 95
        · exact mem_closure_three.mpr ⟨19, 0, 0, by decide⟩
      -- then `n = 47`
      · subst h2
        simp only [Nat.reduceEqDiff, or_self, or_false, or_true, true_and]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        -- can't sum to 91
        · simp only [mem_closure_three, not_exists]
          intro a b c
          by_cases hb : b ≤ 2
          by_cases hc : c ≤ 2
          · interval_cases b <;> interval_cases c <;> omega
          · omega
          · omega
        -- can sum to 92
        · exact mem_closure_three.mpr ⟨9, 1, 0, by decide⟩
        -- can sum to 93
        · exact mem_closure_three.mpr ⟨9, 0, 1, by decide⟩
        -- can sum to 94
        · exact mem_closure_three.mpr ⟨0, 2, 0, by decide⟩
        -- can sum to 95
        · exact mem_closure_three.mpr ⟨0, 1, 1, by decide⟩