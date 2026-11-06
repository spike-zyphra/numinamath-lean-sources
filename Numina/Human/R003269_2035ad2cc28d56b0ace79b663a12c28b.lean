import Mathlib


/- 【Question 29】
8 different positive integers, among which there are at least: 6 multiples of 2, 5 multiples of 3, 3 multiples of 5, 1 multiple of 7.
To make the maximum number among the 8 numbers as small as possible, then this maximum number is $\qquad$. -/
theorem number_theory_165566 : IsLeast {m : ℕ |
    ∃ s : Finset ℕ, s.card = 8 ∧ (∀ x ∈ s, 0 < x) ∧
    6 ≤ (s.filter (2 ∣ ·)).card ∧ 5 ≤ (s.filter (3 ∣ ·)).card ∧
    3 ≤ (s.filter (5 ∣ ·)).card ∧ 1 ≤ (s.filter (7 ∣ ·)).card ∧ s.max = m} 20 := by

  constructor

  · simp only [Finset.one_le_card, Set.mem_setOf_eq, Nat.cast_ofNat]
    -- a possible answer is {6,9,10,12,14,15,18,20}
    use {6,9,10,12,14,15,18,20}
    native_decide

  · simp only [lowerBounds, Finset.one_le_card,
    Set.mem_setOf_eq, forall_exists_index, and_imp]
    -- suppose maximum of set s is m0.
    rintro m0 s hs spos h1 h2 h3 h4 hm0
    -- if m0 ≥ 20, done.
    by_cases m0lt: m0 ≥ 20
    · exact m0lt
    push_neg at m0lt
    -- otherwise any numbers in s < 20.
    have hlt: ∀x ∈ s, x < 20 := by
      intro x hx
      refine lt_of_le_of_lt ?_ m0lt
      exact Finset.le_max_of_eq hx hm0
    have hlt': s ⊆ (Finset.range 20).erase 0 := by
      intro x hx
      simp [hlt x hx, (spos x hx).ne']
    -- then multiples of 5 is 5,10,15.
    replace h3: s.filter (5 ∣ · ) = {5,10,15} := by
      have hh1: s.filter (5 ∣ · ) ⊆ ((Finset.range 20).erase 0).filter (5 ∣ · ) :=
        Finset.filter_subset_filter _ hlt'
      have hh2: ((Finset.range 20).erase 0).filter (5 ∣ · ) = {5,10,15} := by
        native_decide
      rwa [hh2, Finset.subset_iff_eq_of_card_le] at hh1
      simp [h3]
    -- and we claim at least 3 elments are multiples of 6.
    have h5: 3 ≤ ((s.filter (2 ∣ ·)) ∩ (s.filter (3 ∣ ·))).card := by
      rw [Finset.card_inter]
      have: ((s.filter (2 ∣ ·)) ∪ (s.filter (3 ∣ ·))).card ≤ 8 := by
        rw [← hs]
        apply Finset.card_le_card ?_
        refine Finset.union_subset ?_ ?_
        <;> simp
      clear * - h1 h2 this
      omega
    replace h5: 3 ≤ (s.filter (6 ∣ · )).card := by
      suffices (s.filter (2 ∣ ·)) ∩ (s.filter (3 ∣ ·)) =
        s.filter (6 ∣ · ) by
        rwa [this] at h5
      ext x
      have hh1: 6 = 2*3 := by norm_num
      have hh2: Nat.Coprime 2 3 := by norm_num
      rw [hh1]
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor <;> intro h
      · simp only [h, - Nat.reduceMul, hh2.mul_dvd_of_dvd_of_dvd, true_and]
      · simp only [h, true_and]
        constructor <;> exact Dvd.dvd.trans (by norm_num) h.right
    replace h5: s.filter (6 ∣ · ) = {6,12,18} := by
      have hh1: s.filter (6 ∣ · ) ⊆ ((Finset.range 20).erase 0).filter (6 ∣ · ) :=
        Finset.filter_subset_filter _ hlt'
      have hh2: ((Finset.range 20).erase 0).filter (6 ∣ · ) = {6,12,18} := by
        native_decide
      rwa [hh2, Finset.subset_iff_eq_of_card_le] at hh1
      simp [h5]
    -- multiple of 7 is in s, then 7 or 14 is in s.
    replace h4: 7 ∈ s ∨ 14 ∈ s := by
      rcases h4 with ⟨x, hx⟩
      simp only [Finset.mem_filter] at hx
      suffices x = 7 ∨ x = 14 by
        rcases this with hh | hh
        <;> simp [← hh, hx.left]
      specialize spos x hx.left
      specialize hlt x hx.left
      have := hx.right
      clear * - spos this hlt
      revert this spos
      native_decide +revert
    -- at least 6 numbers from s divided by 2, so the 7-multiple must be 14.
    replace h4: 14 ∈ s := by
      refine h4.resolve_left ?_
      rintro h4
      have hh1: {5,10,15, 6, 12,18, 7} ⊆ s := by
        have: ({5,10,15,6,12,18,7}: Finset ℕ) =
          ({5,10,15} ∪ {6,12,18}) ∪ {7} := by native_decide
        rw [this]
        refine Finset.union_subset ?_ (by simp [h4])
        rw [← h3, ← h5]
        refine Finset.union_subset ?_ ?_
        <;> simp
      obtain ⟨x0, hx0, hh2⟩: ∃ x0 ∈ s, x0 ∉ ({5,10,15,6,12,18,7}: Finset ℕ) := by
        apply Finset.exists_of_ssubset ?_
        refine Finset.ssubset_iff_subset_ne.mpr (And.intro hh1 ?_)
        rintro hh2
        simp [← hh2] at hs
      have hh3: s = insert x0 ({5,10,15,6,12,18,7}: Finset ℕ) := by
        refine (Finset.erase_eq_iff_eq_insert hx0 hh2).mp ?_
        symm
        rw [← Finset.subset_iff_eq_of_card_le]
        · rw [Finset.subset_erase]
          exact ⟨hh1, hh2⟩
        · rw [Finset.card_erase_of_mem hx0, hs]
          simp
      have: Finset.filter (2 ∣ · ) {5,10,15,6,12,18,7} = {10,6,12,18} := by
        native_decide
      rw [hh3, Finset.filter_insert, this] at h1
      absurd h1
      push_neg
      by_cases hh: 2 ∣ x0
      · rw [if_pos hh]
        have := Finset.card_insert_le x0 ({10,6,12,18}: Finset ℕ)
        simp only [Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
          not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
          Nat.reduceAdd] at this
        exact Nat.lt_add_one_of_le this
      · rw [if_neg hh]
        simp
    -- thus 7 numbers are determined.
    have h6: {5,10,15,6,12,18,14} ⊆ s := by
      have: ({5,10,15,6,12,18,14}: Finset ℕ) =
        ({5,10,15} ∪ {6,12,18}) ∪ {14} := by native_decide
      rw [this]
      refine Finset.union_subset ?_ (by simp [h4])
      rw [← h3, ← h5]
      refine Finset.union_subset ?_ ?_
      <;> simp
    obtain ⟨x0, hx0, h7⟩: ∃ x0 ∈ s, x0 ∉ ({5,10,15,6,12,18,14}: Finset ℕ) := by
      apply Finset.exists_of_ssubset ?_
      refine Finset.ssubset_iff_subset_ne.mpr (And.intro h6 ?_)
      rintro hh2
      simp [← hh2] at hs
    replace h6: s = insert x0 ({5,10,15,6,12,18,14}: Finset ℕ) := by
      refine (Finset.erase_eq_iff_eq_insert hx0 h7).mp ?_
      symm
      rw [← Finset.subset_iff_eq_of_card_le]
      · rw [Finset.subset_erase]
        exact ⟨h6, h7⟩
      · rw [Finset.card_erase_of_mem hx0, hs]
        simp
    -- to satisfy divided by 2,3 condition, we claim this x0 must be multiple of 6.
    have hx01: 2 ∣ x0 := by
      have: Finset.filter (2 ∣ · ) {5,10,15,6,12,18,14} = {10,6,12,18,14} := by
        native_decide
      rw [h6, Finset.filter_insert, this] at h1
      by_contra!
      rw [if_neg this] at h1
      simp at h1
    have hx02: 3 ∣ x0 := by
      have: Finset.filter (3 ∣ · ) {5,10,15,6,12,18,14} = {15,6,12,18} := by
        native_decide
      rw [h6, Finset.filter_insert, this] at h2
      by_contra!
      rw [if_neg this] at h2
      simp at h2
    -- then we reach a contradiction.
    have: ∀y, y < 20 → 0 < y → 2 ∣ y → 3 ∣ y →
      y ∈ ({5,10,15,6,12,18,14}: Finset ℕ) := by native_decide
    specialize this x0 (hlt x0 hx0) (spos x0 hx0) hx01 hx02
    exfalso; exact h7 this