import Mathlib
open Finset
def tens (n : Fin 100) : Fin 10 := ⟨n.val / 10, Nat.div_lt_of_lt_mul n.isLt⟩
def units (n : Fin 100) : Fin 10 := ⟨n.val % 10, Nat.mod_lt _ (by decide)⟩
def fromDigits (d1 d2 : Fin 10) : Fin 100 :=
  ⟨10 * d1.val + d2.val,
   calc 10 * d1.val + d2.val ≤ 10 * 9 + 9 := by gcongr; exact Nat.le_of_lt_succ d1.isLt; exact Nat.le_of_lt_succ d2.isLt
                         _ = 99           := by rfl
                         _ < 100          := by decide⟩
@[simp] lemma tens_fromDigits (d1 d2 : Fin 10) : tens (fromDigits d1 d2) = d1 := by
  apply Fin.eq_of_val_eq
  simp [tens, fromDigits, Nat.add_div_of_dvd_left]
  omega
@[simp] lemma units_fromDigits (d1 d2 : Fin 10) : units (fromDigits d1 d2) = d2 := by
  apply Fin.eq_of_val_eq
  simp [units, fromDigits, Nat.add_mod_right]
  omega
lemma eq_fromDigits (n : Fin 100) : fromDigits (tens n) (units n) = n := by
  apply Fin.eq_of_val_eq
  simp [fromDigits, tens, units, Nat.div_add_mod]
lemma fromDigits_inj : Function.Injective2 fromDigits := by
  intro d1 d2 d1' d2' h
  have h_tens : tens (fromDigits d1 d1') = tens (fromDigits d2 d2') := by rw [h]
  have h_units : units (fromDigits d1 d1') = units (fromDigits d2 d2') := by rw [h]
  simp at h_tens h_units
  exact ⟨h_tens, h_units⟩
def crossword_numbers (d1 d2 d3 d4 : Fin 10) : Finset (Fin 100) :=
  {fromDigits d1 d2, fromDigits d3 d4, fromDigits d1 d3, fromDigits d2 d4}
def can_be_filled_by (S : Finset (Fin 100)) (d1 d2 d3 d4 : Fin 10) : Prop :=
  crossword_numbers d1 d2 d3 d4 ⊆ S
def can_fill (S : Finset (Fin 100)) : Prop :=
  ∃ d1 d2 d3 d4 : Fin 10, can_be_filled_by S d1 d2 d3 d4
def PropertyA (S : Finset (Fin 100)) : Prop := ¬ can_fill S
def first_digits (S : Finset (Fin 100)) : Finset (Fin 10) := S.image tens
def last_digits (S : Finset (Fin 100)) : Finset (Fin 10) := S.image units
theorem property_A_iff_disjoint_digits (S : Finset (Fin 100)) :
    PropertyA S ↔ Disjoint (first_digits S) (last_digits S) := by
  rw [PropertyA,Finset.disjoint_left]
  rw [not_iff_comm]
  simp
  symm
  constructor
  · 
    intro h_can_fill
    rcases h_can_fill with ⟨d1, d2, d3, d4, h_filled⟩
    rw [can_be_filled_by, subset_iff] at h_filled
    have h1 : (fromDigits d1 d2) ∈ crossword_numbers d1 d2 d3 d4 := by
      simp only [crossword_numbers,mem_insert,mem_singleton,true_or]
    have h2 : (fromDigits d2 d4) ∈ crossword_numbers d1 d2 d3 d4 := by
      simp only [crossword_numbers,mem_insert,mem_singleton,or_true]
    specialize h1
    specialize h2
    use d2
    constructor
    · 
      rw [first_digits, mem_image]
      use fromDigits d2 d4
      simp_all only [tens_fromDigits, and_self]
    · 
      rw [last_digits, mem_image]
      use fromDigits d1 d2
      simp_all only [units_fromDigits, and_self]
  ·
    intro h_not_disjoint
    rcases h_not_disjoint with ⟨b, hb_first, hb_last⟩
    rw [first_digits, mem_image] at hb_first
    rw [last_digits, mem_image] at hb_last
    rcases hb_first with ⟨n_bc, hn_bc_S, h_tens_nbc_eq_b⟩
    rcases hb_last with ⟨n_ab, hn_ab_S, h_units_nab_eq_b⟩
    let c := units n_bc
    let a := tens n_ab
    have h_nbc_form : n_bc = fromDigits b c := by rw [← h_tens_nbc_eq_b, eq_fromDigits]
    have h_nab_form : n_ab = fromDigits a b := by rw [← h_units_nab_eq_b, eq_fromDigits]
    use a, b, b, c
    rw [can_be_filled_by, crossword_numbers, subset_iff]
    intro x hx_mem
    simp only [mem_insert, mem_singleton] at hx_mem
    rcases hx_mem with (rfl|rfl|rfl|rfl)
    · 
      rw [← h_nab_form]; exact hn_ab_S
    · 
      rw [← h_nbc_form]; exact hn_bc_S
    · 
      rw [← h_nab_form]; exact hn_ab_S
    · 
      rw [← h_nbc_form]; exact hn_bc_S
lemma card_S_le_card_F_mul_card_L (S : Finset (Fin 100)) :
    S.card ≤ (first_digits S).card * (last_digits S).card := by
  let f : Fin 100 → Fin 10 × Fin 10 := fun n => (tens n, units n)
  have h_inj_on_S : Set.InjOn f S := by
    intro n1 hn1 n2 hn2 heq_pair
    rw [Prod.ext_iff] at heq_pair
    rw [← eq_fromDigits n1, ← eq_fromDigits n2]
    simp [f] at heq_pair
    rw [heq_pair.1, heq_pair.2]
  calc
    S.card = (S.image f).card := by exact (card_image_of_injOn h_inj_on_S).symm
    _ ≤ ( (S.image tens) ×ˢ (S.image units) ).card := by
        apply Finset.card_le_card
        intro p hp_img
        rw [mem_image] at hp_img
        rcases hp_img with ⟨n, hnS, rfl⟩
        simp [first_digits, last_digits, mem_product, mem_image_of_mem _ hnS]
    _ = (first_digits S).card * (last_digits S).card := by simp [first_digits, last_digits, card_product]
lemma k_mul_10_minus_k_le_25 (k : ℕ) (hk : k ≤ 10) : k * (10 - k) ≤ 25 := by interval_cases k <;> omega
theorem max_elements_is_25 :
    IsGreatest { N : Nat | ∃ (S : Finset (Fin 100)), PropertyA S ∧ N = S.card } 25 := by
  constructor
  · simp only [Set.mem_setOf_eq] 
    let F0 : Finset (Fin 10) := (univ : Finset (Fin 5)).map (Fin.castLEEmb (by omega : 5 ≤ 10))
    let L0_emb : Fin 5 ↪ Fin 10 := {
      toFun := fun (i : Fin 5) => (⟨i.val + 5, by omega⟩ : Fin 10),
      inj' := by
        intro i j h_eq_fin
        simp_all only [Fin.mk.injEq, add_left_inj]
        ext : 1
        simp_all only
    }
    let L0 : Finset (Fin 10) := (univ : Finset (Fin 5)).map L0_emb
    have hF0_card : F0.card = 5 := by
      simp_all only [card_map, card_univ, Fintype.card_fin, F0]
    have hL0_card : L0.card = 5 := by
      simp_all only [card_map, card_univ, Fintype.card_fin, F0, L0, L0_emb]
    have h_disj_F0_L0 : Disjoint F0 L0 := by native_decide
    let product_to_fromDigits_fn : (Fin 10 × Fin 10) → Fin 100 :=
      fun p => fromDigits p.1 p.2
    let S_example := (F0 ×ˢ L0).image product_to_fromDigits_fn
    have hS_example_card : S_example.card = 25 := by
      simp_all only [card_map, card_univ, Fintype.card_fin, F0, L0, L0_emb, S_example, product_to_fromDigits_fn]
      rfl
    use S_example
    constructor
    · 
      rw [property_A_iff_disjoint_digits]
      have h_first_digits_eq_F0 : first_digits S_example = F0 := by
        ext x_digit 
        simp_rw [first_digits, mem_image]
        constructor
        · intro ha
          rcases ha with ⟨n, hn, h_eq_x⟩
          rw [mem_image] at hn
          rcases hn with ⟨p_orig, hp_orig_in_prod, hn_eq_fromDigits_p⟩
          rw [mem_product] at hp_orig_in_prod
          rcases hp_orig_in_prod with ⟨hd1_in_F0, hd2_in_L0⟩
          rw [← hn_eq_fromDigits_p] at h_eq_x
          rw [tens_fromDigits p_orig.1 p_orig.2] at h_eq_x
          rw [← h_eq_x]
          exact hd1_in_F0
        · intro ha
          obtain ⟨d2_val_in_L0, hd2_mem_L0⟩ : ∃ d2, d2 ∈ L0 := by
            apply Finset.Nonempty.exists_mem
            rw [← Finset.card_pos, hL0_card]
            norm_num
          use fromDigits x_digit d2_val_in_L0
          constructor
          · rw [mem_image]
            use (x_digit, d2_val_in_L0)
            constructor
            · 
              rw [mem_product]
              exact ⟨ha, hd2_mem_L0⟩ 
            · 
              rfl
          · 
            rw [tens_fromDigits]
      have h_last_digits_eq_L0 : last_digits S_example = L0 := by
        ext y_digit 
        simp_rw [last_digits, mem_image]
        constructor
        · intro ha
          rcases ha with ⟨n, hn, h_eq_x⟩
          rw [mem_image] at hn
          rcases hn with ⟨p_orig, hp_orig_in_prod, hn_eq_fromDigits_p⟩
          rw [mem_product] at hp_orig_in_prod
          rcases hp_orig_in_prod with ⟨hd1_in_F0, hd2_in_L0⟩
          rw [← hn_eq_fromDigits_p] at h_eq_x
          rw [units_fromDigits p_orig.1 p_orig.2] at h_eq_x
          rw [← h_eq_x]
          exact hd2_in_L0
        · intro hy_digit_in_L0 
          obtain ⟨d1_choice, hd1_choice_in_F0⟩ : ∃ d1, d1 ∈ F0 := by 
            apply Finset.Nonempty.exists_mem 
            rw [← Finset.card_pos, hF0_card] 
            norm_num 
          use fromDigits d1_choice y_digit
          constructor
          · 
            rw [mem_image] 
            use (d1_choice, y_digit)
            constructor
            · 
              rw [mem_product] 
              exact ⟨hd1_choice_in_F0, hy_digit_in_L0⟩
            · 
              simp only [product_to_fromDigits_fn]
          · 
            rw [units_fromDigits] 
      rw [h_first_digits_eq_F0, h_last_digits_eq_L0]
      exact h_disj_F0_L0
    · 
      rw [Eq.comm]
      exact hS_example_card
  · intro N hN_mem_set 
    simp only [Set.mem_setOf_eq] at hN_mem_set
    rcases hN_mem_set with ⟨S_hyp, h_propA_Shyp, rfl⟩
    rw [property_A_iff_disjoint_digits] at h_propA_Shyp
    apply le_trans (card_S_le_card_F_mul_card_L S_hyp)
    let Fcard := (first_digits S_hyp).card
    let Lcard := (last_digits S_hyp).card
    have hFcard_le_10 : Fcard ≤ 10 := Finset.card_le_univ (first_digits S_hyp)
    have hLcard_le_10_minus_Fcard : Lcard ≤ 10 - Fcard := by
      have disj_F_L : Disjoint (first_digits S_hyp) (last_digits S_hyp) := h_propA_Shyp
      calc
        Lcard = (last_digits S_hyp).card := by simp
        _ ≤ (univ \ (first_digits S_hyp)).card := by
          apply Finset.card_le_card
          let F := first_digits S_hyp
          let L := last_digits S_hyp
          rw [disjoint_iff_inter_eq_empty] at disj_F_L 
          intro x hx
          simp at hx ⊢ 
          by_contra h
          have h1 : x ∈ F := h 
          have h2 : x ∈ L := hx 
          have h3 : x ∈ F ∩ L := by 
            simp [Finset.mem_inter, h1, h2] 
          have h4 : x ∉ F ∩ L := by 
            rw [disj_F_L] 
            simp 
          contradiction
        _ = (univ : Finset (Fin 10)).card - (first_digits S_hyp).card := by rw [card_sdiff (subset_univ (first_digits S_hyp))]
        _ = 10 - Fcard := by simp [Fintype.card_fin 10, Fcard] 
    apply Nat.le_trans (Nat.mul_le_mul_left Fcard hLcard_le_10_minus_Fcard)
    exact k_mul_10_minus_k_le_25 Fcard hFcard_le_10