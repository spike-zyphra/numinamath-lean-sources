import Mathlib

open Finset Real

/- Let $a_{1}, a_{2}, \ldots, a_{n}$ and $b_{1}, b_{2}, \ldots, b_{n}$ be two finite sequences consisting of $2 n$ different real numbers. Rearranging each of the sequences in the increasing order we obtain $a_{1}^{\prime}, a_{2}^{\prime}, \ldots, a_{n}^{\prime}$ and $b_{1}^{\prime}, b_{2}^{\prime}, \ldots, b_{n}^{\prime}$. Prove that

$$
\max _{1 \leq i \leq n}\left|a_{i}-b_{i}\right| \geq \max _{1 \leq i \leq n}\left|a_{i}^{\prime}-b_{i}^{\prime}\right| .
$$ -/
theorem inequalities_240577 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i j, a i = a j → i = j) (hb : ∀ i j, b i = b j → i = j)
    (hab : ∀ i j, a i ≠ b j)
    (a' b' : Fin n → ℝ)
    (ha' : ∀ i, a' i = (List.ofFn a).mergeSort[i]'(by simp))
    (hb' : ∀ i, b' i = (List.ofFn b).mergeSort[i]'(by simp)) :
    sSup {|a i - b i| | i} ≥ sSup {|a' i - b' i| | i} := by
  -- simplify the goal
  have hne1 : (univ.image (fun i => |a i - b i|)).Nonempty := by
    use |a ⟨0, hn⟩ - b ⟨0, hn⟩|
    simp only [mem_image, mem_univ, true_and]
    use ⟨0, hn⟩
  have hne2 : (univ.image (fun i => |a' i - b' i|)).Nonempty := by
    use |a' ⟨0, hn⟩ - b' ⟨0, hn⟩|
    simp only [mem_image, mem_univ, true_and]
    use ⟨0, hn⟩
  have h1 : sSup {|a i - b i| | i} = (univ.image (fun i => |a i - b i|)).max' hne1 := by
    apply le_antisymm
    · apply csSup_le
      · use |a ⟨0, hn⟩ - b ⟨0, hn⟩|
        simp only [Set.mem_setOf_eq, exists_apply_eq_apply]
      · intro x hx
        simp only [Set.mem_setOf_eq] at hx
        apply le_max'
        apply mem_image.mpr
        obtain ⟨i, hi⟩ := hx
        use i, ?_, hi
        apply mem_univ
    · apply le_csSup
      · use (univ.image (fun i => |a i - b i|)).max' hne1
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        obtain ⟨i, hi⟩ := hx
        apply le_max'
        apply mem_image.mpr
        use i, ?_, hi
        apply mem_univ
      · apply Set.mem_of_mem_of_subset (s := image (fun i ↦ |a i - b i|) univ)
        · simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range]
          obtain h := max'_mem _ hne1
          obtain ⟨i, hi⟩ := mem_image.mp h
          use i, hi.2
        · intro x hx
          simp at hx
          simp only [Set.mem_setOf_eq]
          obtain ⟨i, hi⟩ := hx
          use i
  have h2 : sSup {|a' i - b' i| | i} = (univ.image (fun i => |a' i - b' i|)).max' hne2 := by
    apply le_antisymm
    · apply csSup_le
      · use |a' ⟨0, hn⟩ - b' ⟨0, hn⟩|
        simp only [Set.mem_setOf_eq, exists_apply_eq_apply]
      · intro x hx
        simp only [Set.mem_setOf_eq] at hx
        apply le_max'
        apply mem_image.mpr
        obtain ⟨i, hi⟩ := hx
        use i, ?_, hi
        apply mem_univ
    · apply le_csSup
      · use (univ.image (fun i => |a' i - b' i|)).max' hne2
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        obtain ⟨i, hi⟩ := hx
        apply le_max'
        apply mem_image.mpr
        use i, ?_, hi
        apply mem_univ
      · apply Set.mem_of_mem_of_subset (s := image (fun i ↦ |a' i - b' i|) univ)
        · simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range]
          obtain h := max'_mem _ hne2
          obtain ⟨i, hi⟩ := mem_image.mp h
          use i, hi.2
        · intro x hx
          simp at hx
          simp only [Set.mem_setOf_eq]
          obtain ⟨i, hi⟩ := hx
          use i
  rw [h1, h2]
  -- Let $m$ be such index that $\left|a_{m}^{\prime}-b_{m}^{\prime}\right|=\max _{1 \leq i \leq n}\left|a_{i}^{\prime}-b_{i}^{\prime}\right|=c$.
  let c := (univ.image (fun i => |a' i - b' i|)).max' hne2
  have hc : c ∈ univ.image (fun i => |a' i - b' i|) := by apply max'_mem
  obtain ⟨m, _, hm⟩ := mem_image.mp hc
  change (image (fun i ↦ |a i - b i|) univ).max' hne1 ≥ c
  -- Without loss of generality we may assume $a_{m}^{\prime}&gt;b_{m}^{\prime}$.
  wlog h : a' m > b' m generalizing a b a' b' with H
  · push_neg at h
    rcases lt_or_eq_of_le h with h | h
    · obtain H := H b a hb ha (by intro i j; rw [ne_comm]; apply hab j i) b' a' hb' ha'
      have : (fun i ↦ |b i - a i|) = (fun i ↦ |a i - b i|) := by
        ext i
        rw [abs_sub_comm]
      rw [this] at H
      have : (fun i ↦ |b' i - a' i|) = (fun i ↦ |a' i - b' i|) := by
        ext i
        rw [abs_sub_comm]
      rw [this] at H
      apply H hne1 hne2
      · rw [←h1]
        congr
        ext i
        simp [abs_sub_comm]
      · rw [←h2]
        congr
        ext i
        simp [abs_sub_comm]
      · apply max'_mem
      · unfold c at hm
        rw [←hm]
        rw [abs_sub_comm]
      · exact h
    · rw [h] at hm
      rw [←hm, sub_self, abs_zero]
      trans |a m - b m|
      · apply le_max'
        apply mem_image.mpr
        use m
      · apply abs_nonneg
  · -- Consider the numbers $a_{m}^{\prime}, a_{m+1}^{\prime}, \ldots, a_{n}^{\prime}$ and $b_{1}^{\prime}, b_{2}^{\prime}, \ldots, b_{m}^{\prime}$.
    have ha_mono : Monotone a' := by
      intro i j hij
      rw [ha', ha']
      apply List.Sorted.rel_get_of_le
      · apply List.sorted_mergeSort'
      · exact hij
    have hb_mono : Monotone b' := by
      intro i j hij
      rw [hb', hb']
      apply List.Sorted.rel_get_of_le
      · apply List.sorted_mergeSort'
      · exact hij
    have ⟨fa, hinjfa, hfa⟩ : ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ i, a' i = a (f i) := by
      let f (i : Fin n) : Fin n := if h : ∃ j, a j = a' i then h.choose else ⟨0, hn⟩
      have {i : Fin n} : ∃ j, a j = a' i := by
          rw [ha']
          have : ((List.ofFn a).mergeSort fun a b ↦ decide (a ≤ b))[i] ∈ List.ofFn a := by
            apply List.mem_mergeSort.mp
            apply List.get_mem
          obtain ⟨j, hj⟩ := List.mem_iff_get.mp this
          use ⟨j.1, by apply lt_of_lt_of_eq j.2; simp⟩
          rw [←hj]
          simp only [List.get_eq_getElem, List.getElem_ofFn]
      have heq : ∀ i, a' i = a (f i) := by
        intro i
        unfold f
        rw [dif_pos this, eq_comm, this.choose_spec]
      use f
      constructor
      · apply Function.Bijective.injective
        apply Nat.bijective_iff_surjective_and_card _|>.mpr
        constructor
        · intro i
          have : a i ∈ (List.ofFn a).mergeSort := by
            apply List.mem_mergeSort.mpr
            apply List.mem_ofFn _ _ |>.mpr
            simp
          obtain ⟨j, hj⟩ := List.mem_iff_get.mp this
          use ⟨j, by apply lt_of_lt_of_eq j.2; simp⟩
          apply ha
          rw [←hj, ←heq, ha']
          congr
        · simp
      · exact heq
    have ⟨gb, hinjgb, hgb⟩ : ∃ g : Fin n → Fin n, Function.Injective g ∧ ∀ i, b' i = b (g i) := by
      let g (i : Fin n) : Fin n := if h : ∃ j, b j = b' i then h.choose else ⟨0, hn⟩
      have {i : Fin n} : ∃ j, b j = b' i := by
          rw [hb']
          have : ((List.ofFn b).mergeSort fun a b ↦ decide (a ≤ b))[i] ∈ List.ofFn b := by
            apply List.mem_mergeSort.mp
            apply List.get_mem
          obtain ⟨j, hj⟩ := List.mem_iff_get.mp this
          use ⟨j.1, by apply lt_of_lt_of_eq j.2; simp⟩
          rw [←hj]
          simp only [List.get_eq_getElem, List.getElem_ofFn]
      have heq : ∀ i, b' i = b (g i) := by
        intro i
        unfold g
        rw [dif_pos this, eq_comm, this.choose_spec]
      use g
      constructor
      · apply Function.Bijective.injective
        apply Nat.bijective_iff_surjective_and_card _|>.mpr
        constructor
        · intro i
          have : b i ∈ (List.ofFn b).mergeSort := by
            apply List.mem_mergeSort.mpr
            apply List.mem_ofFn _ _ |>.mpr
            simp
          obtain ⟨j, hj⟩ := List.mem_iff_get.mp this
          use ⟨j, by apply lt_of_lt_of_eq j.2; simp⟩
          apply hb
          rw [←hj, ←heq, hb']
          congr
        · simp
      · exact heq
    let s₁ := (Finset.Ici m).image a'
    let s₂ := (Finset.Iic m).image b'
    have hcard : (s₁ ∪ s₂).card = n + 1 := by
      rw [card_union_of_disjoint]
      · trans (n - m) + (m + 1)
        · congr
          · rw [Finset.card_image_of_injOn]
            · simp
            · intro i _ j _ h
              rw [hfa, hfa] at h
              apply ha at h
              apply hinjfa h
          · rw [Finset.card_image_of_injOn]
            · simp
            · intro i _ j _ h
              rw [hgb, hgb] at h
              apply hb at h
              apply hinjgb h
        · rw [←Nat.add_assoc, Nat.sub_add_cancel]
          exact Fin.is_le'
      · apply Finset.disjoint_left.mpr
        intro a ha
        obtain ⟨x, hx⟩ := mem_image.mp ha
        by_contra hb
        obtain ⟨y, hy⟩ := mem_image.mp hb
        have : a' x = b' y := by rw [hx.2, hy.2]
        rw [hfa, hgb] at this
        apply hab
        apply this
    -- As there are $n+1$ numbers altogether and only $n$ places in the initial sequence there must exist an index $j$ such that we have $a_{j}$ among $a_{m}^{\prime}, a_{m+1}^{\prime}, \ldots, a_{n}^{\prime}$ and $b_{j}$ among $b_{1}^{\prime}, b_{2}^{\prime}, \ldots, b_{m}^{\prime}$.
    let f (x : ℝ) :=
      if h : ∃ i, a' i = x then fa h.choose
      else if h' : ∃ i, b' i = x then gb h'.choose else ⟨0, hn⟩
    have hf : ∀ a ∈ s₁ ∪ s₂, f a ∈ univ := by simp
    obtain ⟨j, _, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := f) (s := s₁ ∪ s₂) (t := univ) hf (n := 1) (by simp [hcard])
    obtain ⟨l, hl, ⟨p, hp, hne⟩⟩ := Finset.one_lt_card.mp hj
    simp at hl hp
    rw [←hm, abs_of_pos (by exact sub_pos.mpr h)]
    -- Now, as $b_{j} \leq b_{m}^{\prime}&lt;a_{m}^{\prime} \leq a_{j}$ we have $\left|a_{j}-b_{j}\right| \geq\left|a_{m}^{\prime}-b_{m}^{\prime}\right|=c$ and $\max _{1 \leq i \leq n}\left|a_{i}-b_{i}\right| \geq c=\max _{1 \leq i \leq n}\left|a_{i}^{\prime}-b_{i}^{\prime}\right|$.
    rcases hl.1 with h | h
    · obtain ⟨j', hj', haj'⟩ := mem_image.mp h
      have haj : a j = l := by
        rw [←hl.2]
        unfold f
        have : ∃ i, a' i = l := by
          obtain ⟨i, hi⟩ := mem_image.mp h
          use i, hi.2
        rw [dif_pos this, ←hfa, this.choose_spec]
      rcases hp.1 with h' | h'
      · have haj' : a j = p := by
          rw [←hp.2]
          unfold f
          have : ∃ i, a' i = p := by
            obtain ⟨i, hi⟩ := mem_image.mp h'
            use i, hi.2
          rw [dif_pos this, ←hfa, this.choose_spec]
        simp [←haj, ←haj'] at hne
      · have hbj' : b j = p := by
          rw [←hp.2]
          unfold f
          have : ¬∃ i, a' i = p := by
            obtain ⟨i, hi⟩ := mem_image.mp h'
            by_contra h
            obtain ⟨j, hj⟩ := h
            rw [←hi.2, hfa, hgb] at hj
            apply hab
            apply hj
          rw [dif_neg this]
          have : ∃ i, b' i = p := by
            obtain ⟨i, hi⟩ := mem_image.mp h'
            use i, hi.2
          rw [dif_pos this]
          rw [←hgb, this.choose_spec]
        trans |a j - b j|
        · apply le_max'
          apply mem_image.mpr
          use j
        · rw [haj, hbj']
          obtain ⟨indl, hindl, hl⟩ := mem_image.mp h
          obtain ⟨indp, hindp, hp⟩ := mem_image.mp h'
          rw [←hl, ←hp]
          have hle₁ : a' m ≤  a' indl := by
            apply ha_mono
            simp at hindl
            exact hindl
          have hle₂ : b' indp ≤ b' m := by
            apply hb_mono
            simp at hindp
            exact hindp
          rw [abs_of_nonneg]
          · rel [hle₁, hle₂]
          · trans a' m - b' m
            · apply le_of_lt
              apply sub_pos.mpr
              assumption
            · rel [hle₁, hle₂]
    · have hbj : b j = l := by
        rw [←hl.2]
        unfold f
        have : ¬∃ i, a' i = l := by
          obtain ⟨i, hi⟩ := mem_image.mp h
          by_contra h
          obtain ⟨j, hj⟩ := h
          rw [←hi.2, hfa, hgb] at hj
          apply hab
          apply hj
        rw [dif_neg this]
        have : ∃ i, b' i = l := by
          obtain ⟨i, hi⟩ := mem_image.mp h
          use i, hi.2
        rw [dif_pos this, ←hgb, this.choose_spec]
      rcases hp.1 with h' | h'
      · have haj' : a j = p := by
          rw [←hp.2]
          unfold f
          have : ∃ i, a' i = p := by
            obtain ⟨i, hi⟩ := mem_image.mp h'
            use i, hi.2
          rw [dif_pos this, ←hfa, this.choose_spec]
        trans |a j - b j|
        · apply le_max'
          apply mem_image.mpr
          use j
        · rw [haj', hbj]
          obtain ⟨indl, hindl, hl⟩ := mem_image.mp h
          obtain ⟨indp, hindp, hp⟩ := mem_image.mp h'
          rw [←hl, ←hp]
          have hle₁ : a' m ≤ a' indp := by
            apply ha_mono
            simp at hindp
            exact hindp
          have hle₂ : b' indl ≤ b' m := by
            apply hb_mono
            simp at hindl
            exact hindl
          rw [abs_of_nonneg]
          · rel [hle₁, hle₂]
          · trans a' m - b' m
            · apply le_of_lt
              apply sub_pos.mpr
              assumption
            · rel [hle₁, hle₂]
      · have hbj' : b j = p := by
          rw [←hp.2]
          unfold f
          have : ¬∃ i, a' i = p := by
            obtain ⟨i, hi⟩ := mem_image.mp h'
            by_contra h
            obtain ⟨j, hj⟩ := h
            rw [←hi.2, hfa, hgb] at hj
            apply hab
            apply hj
          rw [dif_neg this]
          have : ∃ i, b' i = p := by
            obtain ⟨i, hi⟩ := mem_image.mp h'
            use i, hi.2
          rw [dif_pos this]
          rw [←hgb, this.choose_spec]
        simp [←hbj, ←hbj'] at hne
