import Mathlib

/-
  Find the number of subsets $S$ of $\{1,2, \ldots 63\}$ the sum of whose elements is 2008 .
-/
theorem combinatorics_608313 :
    ((Finset.Icc 1 63).powerset.filter (fun S => ∑ s ∈ S, s = 2008)).card = 6 := by 
  have : ((Finset.Icc 1 63).powerset.filter (fun S => ∑ s ∈ S, s = 2008)).card = ((Finset.Icc 1 63).powerset.filter (fun S => ∑ s ∈ S, s = 8)).card := by
    let f : Finset ℕ → Finset ℕ := fun S => (Finset.Icc 1 63) \ S
    have : ((Finset.Icc 1 63).powerset.filter (fun S => ∑ s ∈ S, s = 2008)) = ((Finset.Icc 1 63).powerset.filter (fun S => ∑ s ∈ S, s = 8)).image f := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
      apply Iff.intro
      · intro ⟨hS, H⟩
        use (Finset.Icc 1 63) \ S
        apply And.intro
        apply And.intro
        · exact Finset.sdiff_subset
        · have : ∑ s ∈ Finset.Icc 1 63 \ S, s + ∑ s ∈ S, s = ∑ s ∈ Finset.Icc 1 63, s := Finset.sum_sdiff hS
          have crux : ∑ s ∈ Finset.Icc 1 63, s = 2016 := by 
            have q := Finset.sum_range_id (63 + 1) 
            have : (63 + 1) * (63 + 1 - 1) / 2 = 2016 := by norm_num
            rw [this] at q
            rw [← q]
            rfl
          omega
        · simp only [f]
          exact Finset.sdiff_sdiff_eq_self hS
      · intro ⟨S', ⟨hS', H1⟩, H2⟩
        apply And.intro
        · simp [← H2, f]
        · have q : ∑ s ∈ Finset.Icc 1 63 \ S', s + ∑ s ∈ S', s = ∑ s ∈ Finset.Icc 1 63, s := Finset.sum_sdiff hS'
          have crux : ∑ s ∈ Finset.Icc 1 63, s = 2016 := by 
            have q := Finset.sum_range_id (63 + 1) 
            have : (63 + 1) * (63 + 1 - 1) / 2 = 2016 := by norm_num
            rw [this] at q
            rw [← q]
            rfl
          have : Finset.Icc 1 63 \ S' = S := by exact H2
          rw [this] at q
          omega
    rw [this]
    rw [Finset.card_image_iff]
    intro S1 hS1 S2 hS2 H
    simp only [f] at H
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hS1 hS2
    calc
      _ = Finset.Icc 1 63 \ (Finset.Icc 1 63 \ S1) := Eq.symm (Finset.sdiff_sdiff_eq_self hS1.1)
      _ = Finset.Icc 1 63 \ (Finset.Icc 1 63 \ S2) := by rw [H]
      _ = _ := (Finset.sdiff_sdiff_eq_self hS2.1)
  rw [this]
  have : (Finset.filter (fun S => ∑ s ∈ S, s = 8) (Finset.Icc 1 63).powerset) = (Finset.filter (fun S => ∑ s ∈ S, s = 8) (Finset.Icc 1 8).powerset) := by
    ext S
    apply Iff.intro
    · simp only [Finset.mem_filter, Finset.mem_powerset, and_imp]
      intro hS H
      apply And.intro ?_ H
      apply by_contra
      intro HH
      simp [Finset.subset_iff] at HH hS
      obtain ⟨x, hx, Hx⟩ := HH
      have := hS hx
      have : {x} ⊆ S := by exact Finset.singleton_subset_iff.mpr hx
      have : ∑ s ∈ S, s ≥ x := by
        calc
          _ = ∑ s ∈ S \ {x}, s + ∑ s ∈ {x}, s := by 
            symm
            exact Finset.sum_sdiff this
          _ ≥ _ := by
            have : ∑ s ∈ S \ {x}, s ≥ 0 := by 
              have : ∀ s ∈ S \ {x}, s ≥ 0 := by 
                intro s hs
                simp only [Finset.mem_sdiff, Finset.mem_singleton] at hs
                have := hS hs.1
                linarith
              exact Nat.zero_le (∑ s ∈ S \ {x}, s)
            simp
      have : 1 ≤ x := by 
        specialize hS hx
        linarith
      specialize Hx this
      linarith
    · simp only [Finset.mem_filter, Finset.mem_powerset, and_imp]
      intro hS H
      apply And.intro
      · calc
          _ ⊆ Finset.Icc 1 8 := hS
          _ ⊆ _ := by 
            rw [Finset.Icc_subset_Icc_iff]
            norm_num
            · norm_num
      · exact H
  rw [this]
  rfl