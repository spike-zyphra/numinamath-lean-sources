import Mathlib

/- Determine the gcd of all numbers of the form


$$

(a-b)(b-c)(c-d)(d-a)(a-c)(b-d)

$$


where $a, b, c, d$ are integers. -/
theorem number_theory_151012 : IsGreatest {x | ∀ (a : Fin 4 → ℤ), x ∣ ∏ p in ((Finset.univ : Finset (Fin 4)).product Finset.univ).filter (fun p => p.1 < p.2),
    (a p.1 - a p.2)} 12 := by
  -- first a lemma that a i - a j divides the expression if i ≠ j
  have aux (i j : Fin 4) (a : Fin 4 → ℤ) (h: i ≠ j) : a i - a j ∣ ∏ p in ((Finset.univ : Finset (Fin 4)).product Finset.univ).filter (fun p => p.1 < p.2), (a p.1 - a p.2) := by
    wlog h' : i < j
    . simp at h'
      specialize this j i a h.symm (lt_of_le_of_ne h' h.symm)
      have h' : a i - a j ∣ a j - a i := by
        nth_rw 2 [← neg_sub]
        exact Int.dvd_neg.mpr (Int.dvd_refl _)
      exact Int.dvd_trans h' this
    . rw [show a i - a j = (fun p ↦ a p.1 - a p.2) (i, j) by simp]
      apply Finset.dvd_prod_of_mem
      simp [h']
      apply Finset.mk_mem_product <;> simp
  constructor
  -- first we prove 12 divides all such expression
  . rintro a
    -- we'll show 3 and 4 dividing expression individually
    rw [show (12 : ℤ) = 3 * 4 by norm_num]
    apply IsCoprime.mul_dvd
    . norm_num
      -- we use pidgeonhole principle, taking remainder modulo 3, two of the a i's must both produce same remainder
    . have : ∃ x ∈ Finset.univ (α := Fin 4) , ∃ y ∈ Finset.univ, x ≠ y ∧ (a x) % 3 = (a y) % 3 := by
        apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := Finset.Ico 0 3)
        . simp
        . rintro i hi
          simp; and_intros
          . exact Int.emod_nonneg (a i) (by norm_num)
          . exact Int.emod_lt_of_pos (a i) (by norm_num)
      obtain ⟨x, hx, y, hy, hxy₁, hxy₂⟩ := this
      -- so then 3 ∣ a x - a y and that divides expression
      replace hxy₂ : 3 ∣ a x - a y := by exact Int.ModEq.dvd (id (Eq.symm hxy₂))
      specialize aux x y a hxy₁
      exact Int.dvd_trans hxy₂ aux
      -- for 4's divisibility first note remainder of a i modulo 4 is from 0,1,2,3
    . have h1 : Finset.image (a · % 4) (Finset.univ (α := Fin 4)) ⊆ Finset.Ico 0 4 := by
        rintro b hb; simp at hb; obtain ⟨c, hc⟩ := hb
        simp; and_intros <;> rw [← hc]
        . exact Int.emod_nonneg (a c) (by norm_num)
        . exact Int.emod_lt_of_pos (a c) (by norm_num)
      have h2 : (Finset.image (a · % 4) (Finset.univ (α := Fin 4))).card ≤ 4 := by
        convert_to _ ≤ (Finset.Ico (0 : ℤ) 4).card
        apply Finset.card_le_card
        exact h1
      -- either the number of different remainder modulo 4 is 4 or less then 4
      obtain h | h := lt_or_eq_of_le (h2)
      -- if less than 4, we use pigeonhole again, two a i must produce same remainder
      . have : ∃ x ∈ Finset.univ (α := Fin 4) , ∃ y ∈ Finset.univ, x ≠ y ∧ (a x) % 4 = (a y) % 4 := by
          apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := Finset.image (a · % 4) (Finset.univ (α := Fin 4)))
          . convert h
          . rintro i hi; simp
        obtain ⟨x, hx, y, hy, hxy₁, hxy₂⟩ := this
        -- then 4 ∣ a x - a y and that divides expression
        replace hxy₂ : 4 ∣ a x - a y := by exact Int.ModEq.dvd (id (Eq.symm hxy₂))
        specialize aux x y a hxy₁
        exact Int.dvd_trans hxy₂ aux
      -- if exactly 4, then there are i0, i1, i2, i3 that produce remainder 0, 1, 2, 3
      . convert_to _ = (Finset.Ico (0 : ℤ) 4).card at h
        have h3 := Finset.eq_of_subset_of_card_le h1 (by rw [h])
        have ha0 : 0 ∈ Finset.image (a · % 4) (Finset.univ (α := Fin 4)) := by
          rw [h3]; simp
        simp [- EuclideanDomain.mod_eq_zero] at ha0
        obtain ⟨i0, ha0⟩ := ha0
        have ha1 : 1 ∈ Finset.image (a · % 4) (Finset.univ (α := Fin 4)) := by
          rw [h3]; simp
        simp at ha1
        obtain ⟨i1, ha1⟩ := ha1
        have ha2 : 2 ∈ Finset.image (a · % 4) (Finset.univ (α := Fin 4)) := by
          rw [h3]; simp
        simp at ha2
        obtain ⟨i2, ha2⟩ := ha2
        have ha3 : 3 ∈ Finset.image (a · % 4) (Finset.univ (α := Fin 4)) := by
          rw [h3]; simp
        simp at ha3
        obtain ⟨i3, ha3⟩ := ha3
        -- so 2 ∣ a i2 - a i0 as they have remainder 2, 0
        have hd1 : 2 ∣ a i2 - a i0 := by
          apply Int.dvd_of_emod_eq_zero
          rw [← Int.emod_emod_of_dvd _ (show (2 : ℤ) ∣ 4 by norm_num), Int.sub_emod, ha2, ha0]
          norm_num
        -- so 2 ∣ a i2 - a i0 as they have remainder 3, 1
        have hd2 : 2 ∣ a i3 - a i1 := by
          apply Int.dvd_of_emod_eq_zero
          rw [← Int.emod_emod_of_dvd _ (show (2 : ℤ) ∣ 4 by norm_num), Int.sub_emod, ha3, ha1]
          norm_num
        -- we'll prove (a i2 - a i 0) * (a i3 - a i1) divides expression by caseworking on relative order of i0, i2 and i1, i3
        have : (a i2 - a i0) * (a i3 - a i1) ∣  ∏ p in ((Finset.univ : Finset (Fin 4)).product Finset.univ).filter (fun p => p.1 < p.2), (a p.1 - a p.2) := by
          have hi02 : i0 ≠ i2 := by rintro hi02; rw [hi02] at ha0; rw [ha0] at ha2; norm_num at ha2
          have hi13 : i1 ≠ i3 := by rintro hi13; rw [hi13] at ha1; rw [ha1] at ha3; norm_num at ha3
          obtain hi02 | hi02 := lt_or_gt_of_ne hi02 <;> obtain hi13 | hi13 := lt_or_gt_of_ne hi13
          all_goals clear hd1 hd2 h3 h2 h1 h
          . rw [show (a i2 - a i0) * (a i3 - a i1) = (a i0 - a i2) * (a i1 - a i3) by ring]
            convert_to ∏ p ∈ {(i0, i2), (i1, i3)}, (a p.1 - a p.2) ∣ _
            . have : i2 ≠ i3 := by rintro h; rw [h] at ha2; rw [ha2] at ha3; norm_num at ha3
              simp [this]
            apply Finset.prod_dvd_prod_of_subset
            rintro p hp; simp at hp
            obtain hp | hp := hp
            all_goals rw [hp]; simp [hi02, hi13]; apply Finset.mk_mem_product <;> simp
          . suffices (a i0 - a i2) * (a i3 - a i1) ∣ ∏ p ∈ Finset.filter (fun p => p.1 < p.2) (Finset.univ.product Finset.univ), (a p.1 - a p.2) by
              refine Int.dvd_trans ?_ this
              apply Int.dvd_neg.mp
              ring_nf
              exact Int.dvd_refl _
            convert_to ∏ p ∈ {(i0, i2), (i3, i1)}, (a p.1 - a p.2) ∣ _
            . have : i0 ≠ i3 := by rintro h; rw [h] at ha0; rw [ha0] at ha3; norm_num at ha3
              simp [this]
            apply Finset.prod_dvd_prod_of_subset
            rintro p hp; simp at hp
            obtain hp | hp := hp
            all_goals rw [hp]; simp [hi02, hi13]; apply Finset.mk_mem_product <;> simp
          . suffices (a i2 - a i0) * (a i1 - a i3) ∣ ∏ p ∈ Finset.filter (fun p => p.1 < p.2) (Finset.univ.product Finset.univ), (a p.1 - a p.2) by
              refine Int.dvd_trans ?_ this
              apply Int.dvd_neg.mp
              ring_nf
              exact Int.dvd_refl _
            convert_to ∏ p ∈ {(i2, i0), (i1, i3)}, (a p.1 - a p.2) ∣ _
            . have : i0 ≠ i3 := by rintro h; rw [h] at ha0; rw [ha0] at ha3; norm_num at ha3
              simp [this]
            apply Finset.prod_dvd_prod_of_subset
            rintro p hp; simp at hp
            obtain hp | hp := hp
            all_goals rw [hp]; simp [hi02, hi13]; apply Finset.mk_mem_product <;> simp
          . convert_to ∏ p ∈ {(i2, i0), (i3, i1)}, (a p.1 - a p.2) ∣ _
            . have : i2 ≠ i3 := by rintro h; rw [h] at ha2; rw [ha2] at ha3; norm_num at ha3
              simp [this]
            apply Finset.prod_dvd_prod_of_subset
            rintro p hp; simp at hp
            obtain hp | hp := hp
            all_goals rw [hp]; simp [hi02, hi13]; apply Finset.mk_mem_product <;> simp
        -- finally 2 divides both so 4 divides expression
        have hd := Int.mul_dvd_mul hd1 hd2
        norm_num at hd
        exact Int.dvd_trans hd this
  -- to prove 12 is an upper bound, consider a that maps 0, 1, 2, 3 to 4, 3, 2, 1, then the expression is 12 so x dividing 12 means x ≤ 12
  . rintro x h
    simp at h
    let a (i : Fin 4) := match i with
      | 0 => (4 : ℤ)
      | 1 => (3 : ℤ)
      | 2 => (2 : ℤ)
      | 3 => (1 : ℤ)
    specialize h a
    convert_to x ∣ 12 at h
    apply Int.le_of_dvd (by norm_num) h