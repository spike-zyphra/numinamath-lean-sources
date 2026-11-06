import Mathlib

open Finset

/--
Let M be a finite set of real numbers such that for any two distinct elements x, y ∈ M,
we have x + y ∈ M. Show that the maximum cardinality of M is 3.
-/
theorem finset_sum_closed_max_three {M : Finset ℝ}
  (h_closed : ∀ x (_ : x ∈ M) y (_ : y ∈ M), x ≠ y → x + y ∈ M) :
  M.card ≤ 3 := by

  -- abbreviate the three parts
  let P := M.filter (· > 0)
  let N := M.filter (· < 0)
  let Z := if 0 ∈ M then ({0} : Finset ℝ) else ∅

  have card_pos_neg_zero :
    M.card
  = (M.filter (· > 0)).card
    + (M.filter (· < 0)).card
    + (if 0 ∈ M then 1 else 0) := by

    -- 1) Show M = P ∪ N ∪ Z
    have h_union : M = P ∪ N ∪ Z := by
      ext x
      simp only [mem_union, mem_filter, mem_singleton, if_pos, if_neg,
        and_true, true_and, false_and, imp_true_iff, or_false, or_true, true_or]
      by_cases h0 : x = 0
      · -- the zero case
        simp only [h0, mem_singleton]
        by_cases h : 0 ∈ M
        · simp [h]
          right
          simp [Z, h]
        · simp [h]
          simp [Z, h]
          constructor
          · refine forall_mem_not_eq'.mp ?_
            intro b hb
            have: b>0 := (mem_filter.mp hb).2
            exact Ne.symm (ne_of_lt this)
          · refine forall_mem_not_eq'.mp ?_
            intro b hb
            have: b<0 := (mem_filter.mp hb).2
            exact Ne.symm (ne_of_gt this)

      · -- x ≠ 0, so either x>0 or x<0 iff x∈P or x∈N
        have tri := lt_trichotomy x 0
        cases tri with
        | inl hlt =>
          constructor
          · intro h
            apply Or.inl
            refine Or.inr ?_
            apply mem_filter.mpr
            exact ⟨h, hlt⟩
          · rintro h
            rcases h with (h | h)
            · rcases h with (h | h)
              · exact (mem_filter.mp h).1
              · exact (mem_filter.mp h).1
            · simp [Z] at h
              split_ifs at h with hz
              · simp at h
                exact h ▸ hz
              . simp at h
        | inr h => cases h with
          | inl heq => exact False.elim (h0 heq)
          | inr hgt =>
            constructor
            . intro h
              apply Or.inl
              apply Or.inl
              apply mem_filter.mpr
              exact And.symm ⟨hgt, h⟩

            . intro h
              rcases h with ((h | h) | h)
              · exact (mem_filter.mp h).1
              · exact (mem_filter.mp h).1
              · simp [Z] at h
                split_ifs at h with hz
                · simp at h
                  exact h ▸ hz
                · simp at h


    -- 2) Show P and N are disjoint
    have hPN : Disjoint P N := by
      rw [Finset.disjoint_left]

      intro x hpx hnx

      have h_P : x ∈ M ∧ 0 < x := by
        rwa [Finset.mem_filter] at hpx

      have h_N : x ∈ M ∧ x < 0 := by
        rwa [Finset.mem_filter] at hnx

      exact lt_asymm h_P.2 h_N.2


    -- 3) Show (P ∪ N) and Z are disjoint
    have hPNZ : Disjoint (P ∪ N) Z := by
      rw [Finset.disjoint_right]
      intro x hx
      rw [Finset.not_mem_union]
      constructor
      · intro h
        have h_P : x ∈ M ∧ 0 < x := by
          rwa [Finset.mem_filter] at h

        have h_Z_0 : Z = {0} := by
          simp [Z] at hx
          split_ifs at hx with hz
          · simp at hx
            exact if_pos hz
          · simp at hx

        have h_Z : x = 0 :=by
          rw [h_Z_0] at hx
          simp at hx
          exact hx

        linarith

      · intro h
        have h_N : x ∈ M ∧ x < 0 := by
          rwa [Finset.mem_filter] at h
        have h_Z_0 : Z = {0} := by
          simp [Z] at hx
          split_ifs at hx with hz
          · simp at hx
            exact if_pos hz
          · simp at hx
        have h_Z : x = 0 := by
          rw [h_Z_0] at hx
          simp at hx
          exact hx

        linarith

    -- 4) Now take cardinalities step by step
    calc
      M.card
        = (P ∪ N ∪ Z).card := by rw [h_union]
      _ = ((P ∪ N) ∪ Z).card := by rw [union_assoc]
      _ = (P ∪ N).card + Z.card := by
        exact card_union_of_disjoint hPNZ
      _ = P.card + N.card + Z.card := by
        congr
        exact card_union_of_disjoint hPN
      _ = P.card + N.card + (if 0 ∈ M then 1 else 0) := by
        -- Z.card is 1 if 0 ∈ M, else 0
        dsimp [Z]
        split_ifs <;> simp [*]


    -- At most one positive element.
  have pos_le : (# {x ∈ M | 0 < x} : ℕ) ≤ 1 := by
    by_contra h
    push_neg at h

    have two_pos : 2 ≤ # {x ∈ M | 0 < x} := h

    -- pick the largest positive element
    -- finiteness gives a maximum via well-foundedness on ℝ
    have : ∃ b, b ∈ {x ∈ M | 0 < x} ∧ ∀ a ∈ {x ∈ M | 0 < x}, a ≤ b :=
      let s := {x ∈ M | 0 < x}
      have h_nonempty : s.Nonempty := by
        apply card_pos.mp
        exact zero_lt_two.trans_le two_pos
      let b := s.max' h_nonempty
      have hb : b ∈ s := s.max'_mem h_nonempty
      have hmax : ∀ a ∈ s, a ≤ b := fun a ha => by
        have hb := s.max'_mem h_nonempty
        exact le_max' s a ha
      ⟨b, hb, hmax⟩
    rcases this with ⟨b, hbM, hmax⟩
    have hbpos : 0 < b := by
      simp [Finset.mem_filter] at hbM
      exact hbM.2
    -- choose a second distinct positive a
    have exists_a : ∃ a, a ∈ {x ∈ M | 0 < x} ∧ a ≠ b := by
      have h1 : {x ∈ M | 0 < x}.card > 1 := two_pos
      have h2 : {x ∈ M | 0 < x}.Nonempty := card_pos.mp (zero_lt_one.trans h1)
      exact exists_ne_of_one_lt_card h b

    rcases exists_a with ⟨a, ha, hab⟩
    simp only [mem_filter] at ha hbM
    have ⟨haM, hapos⟩ := ha
    have ⟨hbM', hbpos⟩ := hbM
    -- then a + b > b, but must lie in M, contradiction
    have hsum_mem : a + b ∈ M := by
      rw [add_comm]
      exact h_closed b hbM' a haM (Ne.symm hab)

    have sum_pos : 0 < a + b := by linarith [hapos, hbpos]
    have hmax' : a + b ≤ b := by
      apply hmax
      simp [hsum_mem, hapos, hbpos]
      exact sum_pos
    linarith

  -- At most one negative element (apply to -M)
  have neg_le : (# {x ∈ M | x < 0} : ℕ) ≤ 1 := by
    by_contra h
    push_neg at h
    have two_neg : 2 ≤ # {x ∈ M | x < 0} := h

    have : ∃ b, b ∈ {x ∈ M | x < 0} ∧ ∀ a ∈ {x ∈ M | x < 0}, b ≤ a := by
      let s := {x ∈ M | x < 0}
      have h_nonempty : s.Nonempty := card_pos.mp (zero_lt_one.trans two_neg)
      let b := s.min' h_nonempty
      have hb : b ∈ s := s.min'_mem h_nonempty
      have hmin : ∀ a ∈ s, b ≤ a := by exact fun a a_1 ↦ min'_le s a a_1
      exact ⟨b, hb, hmin⟩

    -- pick the smallest negative element
    rcases this with ⟨b, hb, hmin⟩
    have hb_neg : b < 0 := by
      simp [mem_filter] at hb
      exact hb.2

    -- have a second distinct negative a
    have exists_a : ∃ a, a ∈ {x ∈ M | x < 0} ∧ a ≠ b := by
      have h1 : {x ∈ M | x < 0}.card > 1 := two_neg
      have h2 : {x ∈ M | x < 0}.Nonempty := card_pos.mp (zero_lt_one.trans h1)
      exact exists_ne_of_one_lt_card h1 b

    -- choose a second distinct negative a
    rcases exists_a with ⟨a, ha, hab⟩
    simp only [mem_filter] at ha hb
    have ⟨haM, ha_neg⟩ := ha
    have ⟨hbM, _⟩ := hb

    -- then a + b < 0, but must lie in M, contradiction
    have sum_neg : a + b < 0 := by linarith
    have sum_in_M := h_closed a haM b hbM hab
    have sum_in_neg : a + b ∈ {x ∈ M | x < 0} := by
      refine mem_filter.mpr ?_
      simp [sum_in_M, sum_neg]

    have hmin' : b ≤ a + b := by
      apply hmin
      exact sum_in_neg
    linarith

  -- Zero is at most one element
  have zero_le : (if 0 ∈ M then 1 else 0) ≤ 1 := by
    split_ifs
    all_goals decide

  -- Combine counts: card M = positives + negatives + (if zero)
  have : M.card = (# {x ∈ M | 0 < x} : ℕ) + (# {x ∈ M | x < 0} : ℕ) + (if 0 ∈ M then 1 else 0) := by exact card_pos_neg_zero
  -- conclude ≤ 3
  rw [this]

  -- calculate the upper bound
  calc
    (# {x ∈ M | 0 < x} : ℕ) + (# {x ∈ M | x < 0} : ℕ) + (if 0 ∈ M then 1 else 0)
    ≤ 1 + 1 + 1 := by linarith
