import Mathlib

open Finset

lemma l_in_product {α β : Type*}
    {a : α} {b : β}
    {s1 : Finset α} {s2 : Finset β}
    (ha : a ∈ s1) (hb : b ∈ s2) :
    (a, b) ∈ s1.product s2 := by
  simp only [Finset.product, mem_mk]
  have : {(a, b)} = (Finset.product {a} {b}).val := by rfl
  apply Multiset.singleton_subset.mp
  rw [this]
  apply Finset.product_subset_product
  <;> simp only [singleton_subset_iff, ha, hb]


lemma l_pairwiseDisjoint_iff {s : Set ℕ} {f : ℕ → Finset (ℕ × ℕ × ℕ)} :
    s.PairwiseDisjoint f ↔ ∀ i, i ∈ s → ∀ j, j ∈ s → (f i ∩ f j).Nonempty → i = j := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]

lemma l_calc : ∑ x ∈ Icc 1 1984, ((1984 - x) / 2 + 1 - (x ⊔ ((1984 - 2 * x) / 2 + 1))) = 82005 := by
  native_decide

/- (7) How many types of triangles with integer side lengths and a perimeter of 1984 are there? -/
theorem number_theory_143675
    {perimeter : ℕ} (h_perimeter : perimeter = 1984)
    (candidate_tuples : Finset (ℕ × ℕ × ℕ))
    (h_candidate_tuples : candidate_tuples = (Icc 1 perimeter).product ((Icc 1 perimeter).product (Icc 1 perimeter))) :
    # (candidate_tuples.filter (fun (a, b, c) => a ≤ b ∧ b ≤ c ∧ c < a + b ∧ a + b + c = perimeter)) = 82005 := by

  let query_finset : Finset (ℕ × ℕ × ℕ) := candidate_tuples.filter (fun (a, b, c) => a ≤ b ∧ b ≤ c ∧ c < a + b ∧ a + b + c = perimeter)

  let f : ℕ → Finset (ℕ × ℕ × ℕ) := fun x =>
    candidate_tuples.filter (fun (a, b, c) => a ≤ b ∧ b ≤ c ∧ c < a + b ∧ a + b + c = perimeter ∧ a = x)

  let s : Finset ℕ := Icc 1 perimeter

  have h_s_pairwiseDisjoint_f : (s : Set ℕ).PairwiseDisjoint f := by
    rw [l_pairwiseDisjoint_iff]
    intro i hi j hj h_inter_nonempty
    simp only [coe_Icc, Set.mem_Icc, s] at hi hj
    obtain ⟨⟨a, b, c⟩, ht⟩ := h_inter_nonempty
    simp [f] at ht
    omega

  let g : ℕ → ℕ → Finset (ℕ × ℕ × ℕ) := fun x y =>
    candidate_tuples.filter (fun (a, b, c) => a ≤ b ∧ b ≤ c ∧ c < a + b ∧ a + b + c = perimeter ∧ a = x ∧ b = y)

  have h_s_pairwiseDisjoint_g (x : ℕ) : (s : Set ℕ).PairwiseDisjoint (g x) := by
    rw [l_pairwiseDisjoint_iff]
    intro i hi j hj h_inter_nonempty
    simp only [coe_Icc, Set.mem_Icc, s] at hi hj
    obtain ⟨⟨a, b, c⟩, ht⟩ := h_inter_nonempty
    simp [g] at ht
    omega

  have h_f_card (i : ℕ) : i ∈ s → (f i).card = ((perimeter - i) / 2 + 1 - (max i ((perimeter - 2 * i) / 2 + 1))) := by
    intro hi
    simp only [mem_Icc, s, f] at hi

    let n := (perimeter - i) / 2 + 1 - i
    let min_b := (max i ((perimeter - 2 * i) / 2 + 1))
    let max_b := (perimeter - i) / 2

    apply card_eq_of_bijective (fun x h => ⟨i, min_b + x, perimeter - i - min_b - x⟩)
    . intro ⟨a, b, c⟩ h
      simp [f] at h
      have : min_b ≤ b := by
        simp only [sup_le_iff, min_b, f]
        omega
      use b - min_b, (by omega)
      simp only [Prod.mk.injEq, true_and, f]
      split_ands <;> omega
    . intro j hj
      simp [f, h_candidate_tuples, hi]
      split_ands
      any_goals omega
      . apply l_in_product
        . exact mem_Icc.mpr hi
        . apply l_in_product
          <;> exact mem_Icc.mpr (by omega)
    . intro x y hx hy h
      simp only [Prod.mk.injEq, add_right_inj, true_and, f, min_b] at h
      exact h.1

  let trans_finset := Finset.disjiUnion s f h_s_pairwiseDisjoint_f

  have h_trans_finset_card : trans_finset.card = ∑ i ∈ s, ((perimeter - i) / 2 + 1 - i ⊔ ((perimeter - 2 * i) / 2 + 1)) := by
    rw [card_disjiUnion s f h_s_pairwiseDisjoint_f]
    apply sum_congr rfl
    exact fun x a => h_f_card x a

  trans trans_finset.card
  . congr 1
    ext ⟨a, b, c⟩
    simp only [h_candidate_tuples, mem_filter, disjiUnion_eq_biUnion, mem_biUnion, mem_Icc,
      trans_finset, s, f]
    constructor
    . intro h
      use a
      split_ands
      any_goals omega
      apply l_in_product
      . exact mem_Icc.mpr (by omega)
      . apply l_in_product
        <;> exact mem_Icc.mpr (by omega)
    . intro ⟨x, hx⟩
      split_ands
      any_goals omega
      apply l_in_product
      . exact mem_Icc.mpr (by omega)
      . apply l_in_product
        <;> exact mem_Icc.mpr (by omega)

  simp_rw [h_trans_finset_card, s, h_perimeter]
  exact l_calc
