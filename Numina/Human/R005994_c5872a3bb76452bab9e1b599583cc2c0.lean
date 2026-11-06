import Mathlib

-- Lemma: If $s ∩ t ⊆ u$ and $|s ∩ t| = |u|$, then $s ∩ t = u$.
lemma inter_eq_of_subset_and_card {α : Type} [DecidableEq α] {s t u : Finset α}
  (h_subset : s ∩ t ⊆ u) (h_card : (s ∩ t).card = u.card) : s ∩ t = u := by
  apply Finset.eq_of_subset_of_card_le
  · exact h_subset
  · rw [h_card]

/-An $(l, a)$-design of a set is a collection of subsets of that set such that each subset contains exactly $l$ elements and that no two of the subsets share more than $a$ elements. How many $(2,1)$-designs are there of a set containing 8 elements?-/
theorem combinatorics_611009 {n : ℕ} (hn : n = 8) :
    (Finset.filter (fun S : Finset (Finset (Fin n)) =>
      ∀ t ∈ S, t.card = 2 ∧ ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1)
      (Finset.powerset Finset.univ)).card = 2 ^ 28 := by
  -- Define $T$ as the set of all 2-element subsets of Fin $8$.
  let T := Finset.filter (fun s : Finset (Fin n) => s.card = 2) Finset.univ
  have hT_card : T.card = Nat.choose 8 2 := by
    subst hn
    rfl
  have h_choose_8_2 : Nat.choose 8 2 = 28 := by
    rfl
  -- Prove that $T$ has exactly $28$ elements $(C(8,2) = 28)$.
  have hT_card_28 : T.card = 28 := by
    rw [hT_card, h_choose_8_2]
  have h_inter_condition : ∀ t1 ∈ T, ∀ t2 ∈ T, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1 := by
    intros t1 ht1 t2 ht2 h_ne
    have ht1_card : t1.card = 2 := (Finset.mem_filter.mp ht1).2
    have ht2_card : t2.card = 2 := (Finset.mem_filter.mp ht2).2
    -- Compute intersection cardinality using inclusion-exclusion.
    have h_card_inter : (t1 ∩ t2).card = t1.card + t2.card - (t1 ∪ t2).card := Finset.card_inter t1 t2
    rw [ht1_card, ht2_card] at h_card_inter
    have h_subset : t1 ∩ t2 ⊆ t1 := Finset.inter_subset_left
    have h_subset' : t1 ∩ t2 ⊆ t2 := Finset.inter_subset_right
    have h_union_bound : (t1 ∪ t2).card ≤ t1.card + t2.card := by
      apply le_trans (Finset.card_union_le t1 t2)
      rw [ht1_card, ht2_card]
    rw [ht1_card, ht2_card] at h_union_bound
    apply le_of_not_gt
    intro h_gt_1
    have h_eq_2 : (t1 ∩ t2).card = 2 := by
      rw [h_card_inter]
      -- Establish upper bound for intersection cardinality.
      have h_inter_le_2 : (t1 ∩ t2).card ≤ 2 := by
        have h_le_t1 : (t1 ∩ t2).card ≤ t1.card := Finset.card_mono h_subset
        rw [ht1_card] at h_le_t1
        exact h_le_t1
      nlinarith
    have h_t1_eq_t2 : t1 = t2 := by
      -- Use lemma to prove $t1 ∩ t2 = t1$ and $t1 ∩ t2 = t2$, implying $t1 = t2$.
      have h_t1_eq_inter : t1 ∩ t2 = t1 := inter_eq_of_subset_and_card h_subset (by rw [h_eq_2, ht1_card])
      have h_t2_eq_inter : t1 ∩ t2 = t2 := inter_eq_of_subset_and_card h_subset' (by rw [h_eq_2, ht2_card])
      have h_t2_eq_inter : t1 ∩ t2 = t2:= by
        apply Finset.eq_of_subset_of_card_le
        · exact h_subset'
        · rw [h_eq_2, ht2_card]
      rw [← h_t1_eq_inter, h_t2_eq_inter]
    exact h_ne h_t1_eq_t2
  -- Prove that the filtered set (all (2,1)-designs) equals the powerset of $T$.
  have h_filter_eq_powerset_T : (Finset.filter (fun S : Finset (Finset (Fin n)) =>
      ∀ t ∈ S, t.card = 2 ∧ ∀ t1 ∈ S, ∀ t2 ∈ S, t1 ≠ t2 → (t1 ∩ t2).card ≤ 1)
      (Finset.powerset Finset.univ)) = Finset.powerset T := by
    apply Finset.ext
    intro S
    constructor
    · intro hS
      rw [Finset.mem_filter] at hS
      rw [Finset.mem_powerset]
      intro t ht
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ t, (hS.2 t ht).1⟩
    · intro hS
      rw [Finset.mem_powerset] at hS
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_powerset.mpr (Finset.subset_univ S)
      · intro t ht
        constructor
        · exact (Finset.mem_filter.mp (hS ht)).2
        · intro t1 ht1 t2 ht2 h_ne_t1_t2
          apply h_inter_condition
          · exact hS ht1
          · exact hS ht2
          · exact h_ne_t1_t2
  -- Compute the cardinality of the powerset of $T$.
  have h_powerset_card : (Finset.powerset T).card = 2 ^ T.card := by
    exact Finset.card_powerset T
  -- Combine results to conclude the cardinality is $2^28$.
  rw [h_filter_eq_powerset_T, h_powerset_card, hT_card_28]
