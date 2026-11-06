import Mathlib

open Finset

set_option maxRecDepth 10000 in
/- 10. (NET 1) ${ }^{\text {IMO6 }}$ An international society has its members in 6 different countries. The list of members contains 1978 names, numbered $1,2, \ldots$, 1978. Prove that there is at least one member whose number is the sum of the numbers of two, not necessarily distinct, of his compatriots. -/
theorem combinatorics_23658 (isFrom : Fin 1978 → Fin 6) :
    ∃ i j k : Fin 1978, isFrom i = isFrom j ∧ isFrom j = isFrom k ∧
    (i + 1 : ℕ) = (j + 1 : ℕ) + (k + 1 : ℕ) := by
  -- Assume the opposite.
  by_contra! h_no_triples
  -- Define a set containing all members from a specific country
  let country (c : Fin 6) : Finset (Fin 1978) := {i | isFrom i = c}
  -- Let us define an operation that takes a set X of members and returns a new set Y that satisfies the following properties:
  -- 1. Let A be the country with the most members in X. Then Y is disjoint from A.
  -- 2. All other countries disjointed from X are also disjointed from Y.
  -- By iterating this operation, we can exclude all countries from the set of members while keeping the set Y non-empty which leads to a contradiction.
  let f (X : Finset (Fin 1978)) (disjCountries : Finset (Fin 6))
      (h_nonempty : X.Nonempty) (h_disj : ∀ c ∈ disjCountries, Disjoint X (country c)) :
      (Finset (Fin 1978)) × (Finset (Fin 6)) :=
    -- Find the country that has the most members in X
    let m := Finset.sup' Finset.univ (by simp) (fun (i : Fin 6) ↦ #(country i ∩ X))
    have h := Finset.exists_mem_eq_sup' (f := (fun (i : Fin 6) ↦ #(country i ∩ X))) (show Finset.univ.Nonempty by simp)
    let A := h.choose
    -- Make sure country X contains members from A
    have h' : (country A ∩ X).Nonempty := by
      by_contra h1
      simp at h1
      have h2 := h.choose_spec
      generalize_proofs p1 at h2
      rw [show h.choose = A by rfl] at h2
      simp [h1] at h2
      obtain ⟨x, hx⟩ := h_nonempty
      specialize h2 (isFrom x)
      have hx' : x ∈ country (isFrom x) := by simp [country]
      replace hx : x ∈ (∅ : Finset (Fin 1978)) := by
        rw [← h2]
        rw [Finset.mem_inter]
        exact ⟨hx', hx⟩
      simp at hx
    -- Find the largest member number in country A ∩ X
    let Amax := (country A ∩ X).max' h'
    -- Calculate differences between Amax and other members in country A ∩ X
    let D := ((country A ∩ X).erase Amax).image (fun a ↦ Amax - a - 1)
    (D, insert A disjCountries)
  -- Prove that the differences are disjoint from excluded countries
  have hf1 (X : Finset (Fin 1978)) (disjCountries : Finset (Fin 6))
      (h_nonempty : X.Nonempty) (h_disj : ∀ c ∈ disjCountries, Disjoint X (country c))
      (h_diff : ∀ c ∈ disjCountries, ∀ x1 ∈ X, ∀ x2 ∈ X, x2 < x1 → x1 - x2 - 1 ∉ country c) :
      let ⟨Y, disjCountries'⟩ := f X disjCountries h_nonempty h_disj;
      ∀ c ∈ disjCountries', Disjoint Y (country c) := by
    intro c
    generalize_proofs _ h h' _
    intro hc
    rw [Finset.disjoint_right]
    intro x hx
    simp [country] at hx
    rw [Finset.mem_insert] at hc
    rcases hc with hc | hc
    · -- Case: c is the country we just added (A)
      intro h1
      simp only [mem_image] at h1
      obtain ⟨a, ha, ha'⟩ := h1
      subst ha'
      have : (country h.choose ∩ X).max' h' > a := by
        exact Finset.lt_max'_of_mem_erase_max' _ _ ha
      simp only [mem_erase] at ha
      obtain ⟨ha1, ha2⟩ := ha
      set Amax := (country h.choose ∩ X).max' h'
      -- We found a contradiction in country A (now c)
      have ha_from : isFrom a = c := by
        simp only [mem_inter] at ha2
        apply And.left at ha2
        rw [← hc] at ha2
        simp [country] at ha2
        exact ha2
      have hAmax_from : isFrom Amax = c := by
        have : Amax ∈ (country h.choose ∩ X) := by
          exact max'_mem (country h.choose ∩ X) h'
        simp only [mem_inter] at this
        apply And.left at this
        rw [← hc] at this
        simp [country] at this
        exact this
      -- Use the contradiction assumption
      specialize h_no_triples Amax a (Amax - a - 1) (by simp [ha_from, hAmax_from]) (by simp [hx, ha_from])
      omega
    · -- Case: c is in the previously excluded countries
      intro h1
      simp only [mem_image] at h1
      obtain ⟨a, ha, ha'⟩ := h1
      subst ha'
      have : (country h.choose ∩ X).max' h' > a := by
        exact Finset.lt_max'_of_mem_erase_max' _ _ ha
      simp only [mem_erase] at ha
      obtain ⟨ha1, ha2⟩ := ha
      set Amax := (country h.choose ∩ X).max' h'
      have : Amax ∈ X := by
        suffices Amax ∈ country h.choose ∩ X from mem_of_mem_inter_right this
        exact max'_mem (country h.choose ∩ X) h'
      -- Use the induction hypothesis for differences
      specialize h_diff c hc Amax this a (mem_of_mem_inter_right ha2) (by omega)
      simp [country, hx] at h_diff
  -- Prove that differences of differences are disjoint from excluded countries
  have hf1_diffs (X : Finset (Fin 1978)) (disjCountries : Finset (Fin 6))
      (h_nonempty : X.Nonempty) (h_disj : ∀ c ∈ disjCountries, Disjoint X (country c))
      (h_diff : ∀ c ∈ disjCountries, ∀ x1 ∈ X, ∀ x2 ∈ X, x2 < x1 → x1 - x2 - 1 ∉ country c) :
      let ⟨Y, disjCountries'⟩ := f X disjCountries h_nonempty h_disj;
      ∀ c ∈ disjCountries', ∀ x1 ∈ Y, ∀ x2 ∈ Y, x2 < x1 → x1 - x2 - 1 ∉ country c := by
    intro c
    generalize_proofs _ h h' _
    intro hc x1 hx1 x2 hx2 hx12
    simp only [mem_image] at hx1
    obtain ⟨a1, ha1, ha1'⟩ := hx1
    subst ha1'
    have : (country h.choose ∩ X).max' h' > a1 := by
      exact Finset.lt_max'_of_mem_erase_max' _ _ ha1
    simp only [mem_erase] at ha1
    obtain ⟨ha11, ha12⟩ := ha1
    simp only [mem_image] at hx2
    obtain ⟨a2, ha2, ha2'⟩ := hx2
    subst ha2'
    have : (country h.choose ∩ X).max' h' > a2 := by
      exact Finset.lt_max'_of_mem_erase_max' _ _ ha2
    simp only [mem_erase] at ha2
    obtain ⟨ha21, ha22⟩ := ha2
    set Amax := (country h.choose ∩ X).max' h'
    ring_nf
    rw [Finset.mem_insert] at hc
    rcases hc with hc | hc
    · -- Another contradiction case for country A
      intro h_a_diff
      have ha1_from : isFrom a1 = c := by
        simp only [mem_inter] at ha12
        apply And.left at ha12
        rw [← hc] at ha12
        simp [country] at ha12
        exact ha12
      have ha2_from : isFrom a2 = c := by
        simp only [mem_inter] at ha22
        apply And.left at ha22
        rw [← hc] at ha22
        simp [country] at ha22
        exact ha22
      simp [country] at h_a_diff
      -- Use the contradiction assumption again
      specialize h_no_triples a2 a1 (a2 - a1 - 1) (by simp [ha1_from, ha2_from])
        (by simp [ha1_from]; convert h_a_diff.symm using 2; ring)
      omega
    · -- Use the induction hypothesis
      specialize h_diff c hc a2 (mem_of_mem_inter_right ha22) a1 (mem_of_mem_inter_right ha12) (by omega)
      convert h_diff using 2
      ring
  -- Prove that the size of differences set is large enough using the pigeonhole principle
  have hf2 (X : Finset (Fin 1978)) (disjCountries : Finset (Fin 6)) (h_nonempty : X.Nonempty)
      (h_disj : ∀ c ∈ disjCountries, Disjoint X (country c))
      {n : ℕ} (h_cnt : (6 - disjCountries.card) * n < X.card) :
      let ⟨Y, disjCountries'⟩ := f X disjCountries h_nonempty h_disj;
      Y.card ≥ n := by
    -- All elements in X must be in countries not yet excluded
    have h1 : ∀ x ∈ X, isFrom x ∈ disjCountriesᶜ := by
      intro x hx
      simp
      intro hx'
      specialize h_disj (isFrom x) hx'
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm] at h_disj
      have : x ∈ (∅ : Finset (Fin 1978)) := by
        rw [← h_disj]
        simp [country, hx]
      simp at this
    -- By pigeonhole principle, one country has at least n members
    have h2 : disjCountriesᶜ.card * n < X.card := by
      simpa [Finset.card_compl]
    obtain ⟨A', hA1, hA2⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to h1 h2
    simp
    rw [Finset.card_image_of_injective]
    swap
    · intro x y hxy
      simpa using hxy
    generalize_proofs h h'
    -- Show that we get at least n-1 differences
    trans #(country h'.choose ∩ X) - 1
    swap
    · exact pred_card_le_card_erase
    -- The country chosen has at least n members
    suffices n < #(country h'.choose ∩ X) by omega
    have h3 := h'.choose_spec
    set A := h'.choose
    rw [← h3]
    apply lt_of_lt_of_le hA2
    have : (filter (fun x => isFrom x = A') X) = (country A' ∩ X) := by
      simp [country]
      ext x
      simp
      tauto
    rw [this]
    apply Finset.le_sup' (fun (i : Fin 6) ↦ #(country i ∩ X))
    simp
  -- Prove that we exclude exactly one more country in each step
  have hf3 (X : Finset (Fin 1978)) (disjCountries : Finset (Fin 6)) (h_disj : ∀ c ∈ disjCountries, Disjoint X (country c)) (h_nonempty : X.Nonempty) :
      let ⟨Y, disjCountries'⟩ := f X disjCountries h_nonempty h_disj;
      disjCountries'.card = disjCountries.card + 1 := by
    simp
    apply Finset.card_insert_of_not_mem
    generalize_proofs h h'
    intro h1
    have h2 := h'.choose_spec
    apply h_disj at h1
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm] at h1
    simp [h1] at h2
    obtain ⟨x, hx⟩ := h_nonempty
    specialize h2 (isFrom x)
    have hx' : x ∈ country (isFrom x) := by simp [country]
    replace hx : x ∈ (∅ : Finset (Fin 1978)) := by
      rw [← h2]
      rw [Finset.mem_inter]
      exact ⟨hx', hx⟩
    simp at hx
  -- Initial configuration: all numbers, no excluded countries
  let X0 : Finset (Fin 1978) := Finset.univ
  let C0 : Finset (Fin 6) := ∅
  have h0_disj : ∀ c ∈ C0, Disjoint X0 (country c) := by
    intro c hc
    simp [C0] at hc
  have h0_diffs : ∀ c ∈ C0, ∀ x1 ∈ X0, ∀ x2 ∈ X0, x2 < x1 → x1 - x2 - 1 ∉ country c := by
    intro c hc
    simp [C0] at hc
  -- First iteration:
  let R1 := f X0 C0 (by simp [X0]) h0_disj
  let X1 := R1.1
  let C1 := R1.2
  have h1_disj : ∀ c ∈ C1, Disjoint X1 (country c) := by
    exact hf1 X0 C0 (by simp [X0]) h0_disj h0_diffs
  have h1_diffs : ∀ c ∈ C1, ∀ x1 ∈ X1, ∀ x2 ∈ X1, x2 < x1 → x1 - x2 - 1 ∉ country c := by
    exact hf1_diffs X0 C0 (by simp [X0]) h0_disj h0_diffs
  -- We get at least 329 differences in step 1
  have h1_X_card : X1.card ≥ 329 := by
    exact hf2 X0 C0 (by simp [X0]) (by simp [C0]) (by simp [C0]; unfold X0; rw [Finset.card_fin]; norm_num)
  have h1_C_card : C1.card = 1 := by
    exact hf3 X0 C0 (by simp [C0]) (by simp [X0])
  -- Second iteration:
  let R2 := f X1 C1 (by rw [← Finset.card_ne_zero]; omega) h1_disj
  let X2 := R2.1
  let C2 := R2.2
  have h2_disj : ∀ c ∈ C2, Disjoint X2 (country c) := by
    exact hf1 X1 C1 (by rw [← Finset.card_ne_zero]; omega) h1_disj h1_diffs
  have h2_diffs : ∀ c ∈ C2, ∀ x1 ∈ X2, ∀ x2 ∈ X2, x2 < x1 → x1 - x2 - 1 ∉ country c := by
    exact hf1_diffs X1 C1 (by rw [← Finset.card_ne_zero]; omega) h1_disj h1_diffs
  -- We get at least 65 differences in step 2
  have h2_X_card : X2.card ≥ 65 := by
    apply hf2 X1 C1 (by rw [← Finset.card_ne_zero]; omega) h1_disj
    simp [h1_C_card]
    omega
  have h2_C_card : C2.card = 2 := by
    exact hf3 X1 C1 h1_disj (by rw [← Finset.card_ne_zero]; omega)
  -- Third iteration:
  let R3 := f X2 C2 (by rw [← Finset.card_ne_zero]; omega) h2_disj
  let X3 := R3.1
  let C3 := R3.2
  have h3_disj : ∀ c ∈ C3, Disjoint X3 (country c) := by
    exact hf1 X2 C2 (by rw [← Finset.card_ne_zero]; omega) h2_disj h2_diffs
  have h3_diffs : ∀ c ∈ C3, ∀ x1 ∈ X3, ∀ x2 ∈ X3, x2 < x1 → x1 - x2 - 1 ∉ country c := by
    exact hf1_diffs X2 C2 (by rw [← Finset.card_ne_zero]; omega) h2_disj h2_diffs
  -- We get at least 16 differences in step 3
  have h3_X_card : X3.card ≥ 16 := by
    apply hf2 X2 C2 (by rw [← Finset.card_ne_zero]; omega) h2_disj
    simp [h2_C_card]
    omega
  have h3_C_card : C3.card = 3 := by
    rw [show 3 = #C2 + 1 by simp [h2_C_card]]
    exact hf3 X2 C2 h2_disj (by rw [← Finset.card_ne_zero]; omega)
  -- Fourth iteration:
  let R4 := f X3 C3 (by rw [← Finset.card_ne_zero]; omega) h3_disj
  let X4 := R4.1
  let C4 := R4.2
  have h4_disj : ∀ c ∈ C4, Disjoint X4 (country c) := by
    exact hf1 X3 C3 (by rw [← Finset.card_ne_zero]; omega) h3_disj h3_diffs
  have h4_diffs : ∀ c ∈ C4, ∀ x1 ∈ X4, ∀ x2 ∈ X4, x2 < x1 → x1 - x2 - 1 ∉ country c := by
    exact hf1_diffs X3 C3 (by rw [← Finset.card_ne_zero]; omega) h3_disj h3_diffs
  -- We get at least 5 differences in step 4
  have h4_X_card : X4.card ≥ 5 := by
    apply hf2 X3 C3 (by rw [← Finset.card_ne_zero]; omega) h3_disj
    simp [h3_C_card]
    omega
  have h4_C_card : C4.card = 4 := by
    rw [show 4 = #C3 + 1 by simp [h3_C_card]]
    exact hf3 X3 C3 h3_disj (by rw [← Finset.card_ne_zero]; omega)
  -- Fifth iteration:
  let R5 := f X4 C4 (by rw [← Finset.card_ne_zero]; omega) h4_disj
  let X5 := R5.1
  let C5 := R5.2
  have h5_disj : ∀ c ∈ C5, Disjoint X5 (country c) := by
    exact hf1 X4 C4 (by rw [← Finset.card_ne_zero]; omega) h4_disj h4_diffs
  have h5_diffs : ∀ c ∈ C5, ∀ x1 ∈ X5, ∀ x2 ∈ X5, x2 < x1 → x1 - x2 - 1 ∉ country c := by
    exact hf1_diffs X4 C4 (by rw [← Finset.card_ne_zero]; omega) h4_disj h4_diffs
  -- We get at least 2 differences in step 5
  have h5_X_card : X5.card ≥ 2 := by
    apply hf2 X4 C4 (by rw [← Finset.card_ne_zero]; omega) h4_disj
    simp [h4_C_card]
    omega
  have h5_C_card : C5.card = 5 := by
    rw [show 5 = #C4 + 1 by simp [h4_C_card]]
    exact hf3 X4 C4 h4_disj (by rw [← Finset.card_ne_zero]; omega)
  -- Sixth iteration:
  let R6 := f X5 C5 (by rw [← Finset.card_ne_zero]; omega) h5_disj
  let X6 := R6.1
  let C6 := R6.2
  have h6_disj : ∀ c ∈ C6, Disjoint X6 (country c) := by
    exact hf1 X5 C5 (by rw [← Finset.card_ne_zero]; omega) h5_disj h5_diffs
  -- We get at least 1 difference in step 6
  have h6_X_card : X6.card ≥ 1 := by
    apply hf2 X5 C5 (by rw [← Finset.card_ne_zero]; omega) h5_disj
    simp [h5_C_card]
    omega
  -- We've used all 6 countries
  have h6_C_card : C6.card = 6 := by
    conv => rhs; rw [show 6 = #C5 + 1 by simp [h5_C_card]]
    exact hf3 X5 C5 h5_disj (by rw [← Finset.card_ne_zero]; omega)
  have h6_C_univ : C6 = univ := by
    simpa [← Finset.card_eq_iff_eq_univ]
  -- But we still have a remaining element
  have h6_X_nonempty : X6.Nonempty := by
    rw [← Finset.card_ne_zero]
    omega
  obtain ⟨x, hx⟩ := h6_X_nonempty
  -- This is impossible since we've excluded all countries
  rw [h6_C_univ] at h6_disj
  specialize h6_disj (isFrom x) (by simp)
  apply Finset.disjoint_left.mp at h6_disj
  specialize h6_disj hx
  simp [country] at h6_disj
