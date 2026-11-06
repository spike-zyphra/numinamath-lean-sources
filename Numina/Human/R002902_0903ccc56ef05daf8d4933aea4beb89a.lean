import Mathlib

/-8.5. 20 numbers: $1,2, \ldots, 20$ were divided into two groups. It turned out that the sum of the numbers in the first group is equal to the product of the numbers in the second group. a) What is the smallest and b) what is the largest number of numbers that can be in the second group?-/

-- Lemma: If a finset `S` of natural numbers has at least `n+1` elements,
-- and all elements in `S` are `≥ b+1`, then the maximum element of `S` is `≥ n+b+1`.
lemma lemma1 ( n : ℕ ) { S : Finset ℕ } ( hS₀ : ∀ i ∈ S, b + 1 ≤ i ) ( hS : n  + 1 ≤ S.card )
: n + b + 1 ≤ (S.max' <| Finset.card_pos.mp <| Nat.zero_lt_of_lt hS) := by
  revert S
  induction n with
  | zero =>
    intro S hS₀ hS
    simp only [zero_add] at *
    apply hS₀
    exact Finset.max'_mem S _
  | succ n' ih =>
    intro S hS₀ hS
    set I := S.max' <| Finset.card_pos.mp <| Nat.zero_lt_of_lt hS
    have hI : I ∈ S := Finset.max'_mem S _
    set S' := S.erase I
    replace ih := @ih S' (λ i hi => hS₀ i <| Finset.mem_of_mem_erase hi) (by
      simp only [hI, Finset.card_erase_of_mem, S']
      exact Nat.le_sub_one_of_lt hS
    )
    rw [← add_le_add_iff_right 1, show n' + b + 1 + 1 = n' + 1 + b + 1 by ring_nf] at ih
    apply ih.trans
    clear ih hS₀ b
    refine Order.add_one_le_iff.mpr ?_
    simp only [Finset.max'_lt_iff, I]
    intro i hi
    exact Finset.lt_max'_of_mem_erase_max' S (Finset.card_pos.mp (Nat.zero_lt_of_lt hS)) hi

-- Lemma: If a finset `S` of natural numbers has at least `n` elements,
-- all `≥ b` (where `b > 0`), then the product of elements in `S` is `≥ (n+b-1)! / b!`.
lemma lemma2 ( n : ℕ ) ( hb : 0 < b ) { S : Finset ℕ } ( hS₀ : ∀ i ∈ S, b ≤ i ) ( hS : n ≤ S.card )
: (n + b - 1).factorial / b.factorial ≤ ∏ i ∈ S, i := by
  revert S
  induction n with
  | zero =>
    intro S hS₀ hS
    simp only [zero_add]
    apply (show (b - 1).factorial / b.factorial ≤ 1 by
      refine Nat.div_le_of_le_mul ?_; simp only [mul_one]
      refine Nat.factorial_le ?_
      exact Nat.sub_le b 1
    ).trans
    refine Finset.one_le_prod' ?_
    intro i hi
    haveI := hS₀ i hi
    rw [@Nat.lt_iff_add_one_le] at hb
    linarith
  | succ n' ih =>
    intro S hS₀ hS
    set I : ℕ := S.max' <| Finset.card_pos.mp <| Nat.zero_lt_of_lt hS with hI
    replace ih := @ih (S.erase I) (λ i hi => by
      apply hS₀
      simp_all only [Finset.mem_erase, ne_eq, I]
    ) (by
      have hI : I ∈ S := by
        simp only [I]
        exact Finset.max'_mem S _
      simp only [hI, Finset.card_erase_of_mem, ge_iff_le]
      exact Nat.le_sub_one_of_lt hS
    )
    match b with
    | 0 => contradiction
    | b + 1 =>
      by_cases hn' : n' = 0
      · simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, hn', zero_add,
          add_tsub_cancel_right, add_tsub_cancel_left, ge_iff_le] at *
        rw [Nat.div_self]
        refine Finset.one_le_prod' ?_
        intro i hi; haveI := hS₀ i hi
        exact Nat.one_le_of_lt (hS₀ i hi)
        exact Nat.factorial_pos (b + 1)
      simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, ← add_assoc,
        add_tsub_cancel_right, ge_iff_le] at *; clear hb hI
      rw [add_right_comm, Nat.factorial_succ]
      have hI : (n' + b + 1) ≤ I := by
        clear * - hS₀ hS
        exact lemma1 n' hS₀ hS
      rw [← mul_le_mul_iff_of_pos_right <| Nat.zero_lt_of_lt hI,
      Finset.prod_erase_mul S _ <| Finset.max'_mem S _] at ih
      exact (show (n' + b + 1) * (n' + b).factorial / (b + 1).factorial ≤ (n' + b).factorial / (b + 1).factorial * I by
        rw [Nat.mul_div_assoc, mul_comm _ I]
        exact Nat.mul_le_mul_right ((n' + b).factorial / (b + 1).factorial) hI
        refine Nat.factorial_dvd_factorial ?_
        simp only [add_comm b, add_le_add_iff_right]
        exact Nat.one_le_iff_ne_zero.mpr hn'
      ).trans ih

-- Lemma: If a finset `S` of natural numbers has at least `n` elements,
-- all `≥ 1`, then the product of elements in `S` is `≥ n!`.
lemma lemma3 ( n : ℕ )  { S : Finset ℕ } ( hS₀ : ∀ i ∈ S, 1 ≤ i ) ( hS : n ≤ S.card )
: n.factorial ≤ ∏ i ∈ S, i := by
  haveI := lemma2 n (show 0 < 1 by simp) hS₀ hS
  simp only [add_tsub_cancel_right, Nat.factorial_one, Nat.div_one] at this
  exact this

theorem number_theory_127981 (S1 S2 : Finset ℕ) (hS1 : S1 ⊆ Finset.Icc 1 20)
  (hS2 : S2 ⊆ Finset.Icc 1 20) (hS12 : S1 ∩ S2 = ∅) (hS12' : S1 ∪ S2 = Finset.Icc 1 20)
  (hS1' : ∑ x ∈ S1, x = ∏ x ∈ S2, x) :
  S2.card ≥ 3 ∧ S2.card ≤ 5 := by
  -- S1 is the set of numbers from 1 to 20 that are not in S2.
  have hS_diff : S1 = Finset.Icc 1 20 \ S2 := by
    ext i
    simp_all only [Finset.mem_sdiff, Finset.mem_Icc]
    apply Iff.intro
    · intro a
      apply And.intro
      · apply And.intro
        · haveI := hS1 a
          simp_all only [Finset.mem_Icc]
        · haveI := hS1 a
          simp_all only [Finset.mem_Icc]
      · apply Aesop.BuiltinRules.not_intro
        intro a_1
        rw [@Finset.eq_empty_iff_forall_not_mem] at hS12
        simp_all only [Finset.mem_inter, not_and]
    · intro a
      obtain ⟨left, right⟩ := a
      obtain ⟨left, right_1⟩ := left
      rw [@Finset.ext_iff] at hS12'
      simp only [Finset.mem_union, Finset.mem_Icc] at hS12'
      haveI := hS12' i |>.mpr ⟨left, right_1⟩
      simp_all only [or_false]
  -- The sum of all integers from 1 to 20 is 210.
  -- This is a known arithmetic series sum: 20 * (20+1) / 2 = 10 * 21 = 210.
  have h0 : (∑ i ∈ Finset.Icc 1 20, i) = 210 := rfl
  -- Part a) Show S2.card ≥ 3.
  -- The human proof argues this by eliminating S2.card = 0, 1, 2.
  have h1 : S2.card ≥ 3 := by
    -- Proof by contradiction: assume S2.card < 3.
    by_contra nh; simp only [ge_iff_le, not_le] at nh
    -- Let d be the cardinality of S2.
    set d := S2.card with hd; symm at hd
    -- We consider cases for d = 0, 1, 2, since d < 3 by assumption `nh`.
    match d with
    | 0 =>
      -- Case 1: S2 is empty (S2.card = 0).
      -- If S2 is empty, its product is 1.
      -- S1 becomes Finset.Icc 1 20, so its sum is 210.
      -- The condition hS1' becomes 210 = 1, which is a contradiction.
      rw [@Finset.card_eq_zero] at hd
      simp only [hd, Finset.empty_subset, Finset.inter_empty, Finset.union_empty, Finset.prod_empty,
        Nat.ofNat_pos] at *
      rw [hS12'] at hS1'
      revert hS1'; decide
    | 1 =>
      -- Case 2: S2 has one element (S2.card = 1). Let S2 = {a}.
      -- The product of elements in S2 is 'a'.
      -- The sum of elements in S1 is (sum of all numbers) - a = 210 - a.
      -- The condition hS1' (sum S1 = prod S2) becomes 210 - a = a.
      rw [@Finset.card_eq_one] at hd
      obtain ⟨a, ha⟩ := hd
      simp only [ha, Finset.singleton_subset_iff, Finset.mem_Icc, Finset.prod_singleton,
        Nat.one_lt_ofNat] at *; clear nh ha
      rw [hS_diff] at hS1'
      rw [@Finset.sdiff_singleton_eq_erase] at hS1'
      have ha' : a ∈ Finset.Icc 1 20 := by
        simp only [Finset.mem_Icc]; exact hS2
      -- From 210 - a = a, we add 'a' to both sides: (210 - a) + a = a + a.
      -- This simplifies to 210 = 2*a.
      rw [← add_left_inj a, Finset.sum_erase_add _ _ ha', h0] at hS1'
      rw [← mul_two, show 210 = 105 * 2 from rfl] at hS1'
      rw [mul_eq_mul_right_iff] at hS1'
      simp only [OfNat.ofNat_ne_zero, or_false] at hS1'
      -- So, a = 105. However, 'a' must be in S2, and thus in Finset.Icc 1 20.
      -- 105 is not in [1,20], which is a contradiction.
      subst hS1'; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, and_false] at hS2
    | 2 =>
      -- Case 3: S2 has two elements (S2.card = 2). Let S2 = {a, b}.
      -- The product of elements in S2 is a*b.
      -- The sum of elements in S1 is (sum of all numbers) - a - b = 210 - a - b.
      -- The condition hS1' (sum S1 = prod S2) becomes 210 - a - b = a*b.
      rw [@Finset.card_eq_two] at hd
      obtain ⟨a, b, hab, hS⟩ := hd
      simp only [hS, Finset.union_insert, Nat.lt_add_one, ne_eq] at *
      rw [hS_diff] at hS1'
      simp only [Finset.mem_singleton, hab, not_false_eq_true, Finset.prod_insert,
        Finset.prod_singleton] at hS1'
      change ∑ i ∈ Finset.Icc 1 20 \ (insert a {b}), i = a * b at hS1'
      rw [@Finset.sdiff_insert, @Finset.sdiff_singleton_eq_erase] at hS1'
      rw [@Finset.insert_subset_iff] at hS2
      simp only [Finset.mem_Icc, Finset.singleton_subset_iff] at hS2
      -- Rearranging 210 - a - b = a*b gives 210 = a*b + a + b.
      -- Adding 1 to both sides: 211 = a*b + a + b + 1.
      -- This factors to 211 = (a+1)(b+1).
      rw [← add_left_inj a, Finset.sum_erase_add _ _ (by {
        simp only [Finset.mem_erase, ne_eq, hab, not_false_eq_true, Finset.mem_Icc, true_and]
        exact hS2.1
      }), ← add_left_inj b, Finset.sum_erase_add _ _ (by {
        simp only [Finset.mem_Icc]; exact hS2.2
      }), h0, ← add_left_inj 1, show a * b + a + b + 1 = (a + 1) * (b + 1) by ring_nf] at hS1'
      simp only [Nat.reduceAdd] at hS1'
      -- The human proof notes that 211 is a prime number.
      -- Since a,b are in [1,20], a+1 and b+1 must be in [2,21].
      -- As 211 is prime, its only factor pairs are (1, 211) (and vice-versa). Neither 1 nor 211 are in [2,21].
      -- Thus, there are no integer solutions for a,b in [1,20].
      -- The Lean proof verifies this by checking all possible pairs (a,b) from [1,20]x[1,20] using fin_cases.
      clear * - hS1' hS2
      have ha : 2 ≤ a + 1 := by linarith
      have hb : 2 ≤ b + 1 := by linarith
      clear hS2
      generalize ha' : a + 1 = a'
      generalize hb' : b + 1 = b'
      simp only [ha', hb'] at *; clear ha' hb' a b
      have nh : Nat.Prime 211 := by norm_num
      rw [@Nat.prime_def] at nh
      simp only [Nat.reduceLeDiff, true_and] at nh
      nth_rw 1 [hS1'] at nh
      replace nh := nh a' ⟨b', rfl⟩
      rcases nh with rfl | rfl
      simp only [Nat.not_ofNat_le_one] at ha
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, left_eq_mul₀] at hS1'
      simp only [hS1', Nat.not_ofNat_le_one] at hb
    -- This case `d+3` corresponds to `S2.card = S2.card` when `S2.card ≥ 3`.
    -- `nh` is `S2.card < 3`. If `S2.card = d+3`, then `d+3 < 3` means `d < 0`, impossible for `d:ℕ`.
    | d + 3 => simp only [add_lt_iff_neg_right, not_lt_zero'] at nh
  -- Thus, S2.card must be at least 3. (The human proof provides an example: {1,9,20})

  -- Part b) Show S2.card ≤ 5.
  -- The human proof argues this by showing S2.card ≥ 6 leads to a contradiction.
  have h2 : S2.card ≤ 5 := by
    -- Proof by contradiction: assume S2.card > 5, i.e., S2.card ≥ 6.
    by_contra nh; simp only [not_le] at nh
    -- We will show that this assumption implies sum S1 < prod S2,
    -- which contradicts the given hS1' (sum S1 = prod S2).
    have nh : ∑ i ∈ S1, i < ∏ i ∈ S2, i := by
      -- The sum of numbers in S1 is at most 210.
      -- Human proof: sum S1 = 210 - sum S2. Since elements are from [1,20], sum S2 > 0 (as S2 cannot be empty), so sum S1 < 210.
      -- Lean proof: sum S1 ≤ sum (Finset.Icc 1 20) because S1 ⊆ Finset.Icc 1 20.
      have hl : ∑ i ∈ S1, i ≤ 210 := by
        rw [← h0]; clear * - hS1
        exact Finset.sum_le_sum_of_ne_zero fun x a a_1 => hS1 a
      -- If S2.card ≥ 6, the product of its elements (which are all ≥ 1)
      -- is at least 1*2*3*4*5*6 = 720. (Using lemma3 lemma)
      have hr : 720 ≤ ∏ i ∈ S2, i := by
        change 6 ≤ S2.card at nh
        clear hl h0 hS_diff hS1' hS12' hS12 hS1 S1
        have hS : ∀ i ∈ S2, 1 ≤ i := by
          intro i hi
          replace hi := hS2 hi
          simp only [Finset.mem_Icc] at hi
          simp_all only
        clear hS2
        exact lemma3 6 hS nh
      -- We have sum S1 ≤ 210 and prod S2 ≥ 720. Since 210 < 720, it follows that sum S1 < prod S2.
      clear * - hl hr
      linarith
    -- Substitute hS1' (sum S1 = prod S2) into the inequality sum S1 < prod S2.
    rw [hS1'] at nh
    -- This leads to (prod S2) < (prod S2), which is a contradiction.
    simp only [lt_self_iff_false] at nh
  -- Therefore, S2.card must be at most 5. (The human proof provides an example: {1,2,3,4,8})

  -- Combine the two results.
  exact ⟨h1, h2⟩
