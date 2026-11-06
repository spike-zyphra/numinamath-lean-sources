import Mathlib

def p (a : Fin 2007 → ℕ) (x : ℕ) := ∑ i ∈ Finset.range (x + 1 : ℕ), a i

lemma trac (a : Fin 2007 → ℕ) (h : ∀ s : Finset ℕ, (∀ u, u ∈ s → u < 2007) → 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, a i)) : ∀ s : Finset (Fin 2007), 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, a i) := by
  intro s hs_card
  have h_main : ¬(2008 ∣ ∑ i ∈ s, a i) := by
    -- Step 1: Define s' as the image of s under Fin.val
    have h₁ : ∀ (u : ℕ), u ∈ (Finset.image (fun j : Fin 2007 => j.val) s) → u < 2007 := by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨j, hj, rfl⟩ := hu
      exact j.is_lt
    -- Step 2: Prove that s.card = s'.card
    have h₂ : (Finset.image (fun j : Fin 2007 => j.val) s).card = s.card := by
      apply Finset.card_image_of_injective
      intro j₁ j₂ h_eq
      simpa [Fin.ext_iff] using h_eq
    -- Step 3: Prove that the sums are equal
    have h₃ : ∑ i ∈ s, a i = ∑ k ∈ (Finset.image (fun j : Fin 2007 => j.val) s), a k := by
      apply Eq.symm
      have pt := Finset.sum_image (g := ((fun (j : Fin 2007) => j) : Fin 2007 → ℕ)) (f := (fun (j : ℕ) => a (↑j))) (s := s) (by simp [Fin.val_inj])
      simp [pt]
    -- Step 4: Use h to get that 2008 does not divide the sum over s'
    have h₄ : 1 ≤ (Finset.image (fun j : Fin 2007 => j.val) s).card := by
      rw [h₂]
      exact hs_card
    have h₅ : ¬(2008 ∣ ∑ i ∈ (Finset.image (fun j : Fin 2007 => j.val) s), a i) := by
      apply h (Finset.image (fun j : Fin 2007 => j.val) s) h₁ h₄
    -- Step 5: Conclude that 2008 does not divide the sum over s
    rw [h₃] at *
    exact h₅
  exact h_main

lemma trax (a : Fin 2007 → ℕ) (h : ∀ s : Finset (Fin 2007), 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, a i)) : ∀ s : Finset ℕ, (∀ u, u ∈ s → u < 2007) → 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, a i) := by
  intro s hu h_card
  have h_main : ¬(2008 ∣ ∑ i ∈ s, a i) := by
    -- Construct `s' : Finset (Fin 2007)` from `s` using the hypothesis `hu`
    have h₁ : ∀ (u : ℕ), u ∈ s → u < 2007 := hu
    set s' : Finset (Fin 2007) := s.attach.image (fun x => ⟨x.1, h₁ x.1 x.2⟩) with hs'
    -- Prove that `s'.card = s.card`
    have h₂ : s'.card = s.card := by
      have h₃ : s'.card = s.card := by
        rw [hs']
        -- The mapping is injective, so the cardinality is preserved
        rw [Finset.card_image_of_injective]
        · simp [Finset.card_attach]
        · intro x y hxy
          simp_all [Subtype.ext_iff]
      exact h₃
    -- Prove that `∑ i ∈ s', a i = ∑ i ∈ s, a i`
    have h₃ : ∑ i ∈ s', a i = ∑ i ∈ s, a i := by
      rw [hs']
      -- The sum over `s'` is the same as the sum over `s` because the mapping is injective and the terms are the same
      calc
        _ = ∑ x in s.attach, a ⟨x.1, h₁ x.1 x.2⟩ := by
          rw [Finset.sum_image]
          · simp [Finset.sum_attach]
        _ = ∑ i in s, a i := by
          -- The sum over `s.attach` is the same as the sum over `s` because the terms are the same
          conv => right; rw [← Finset.sum_attach]
          congr
          ext aa
          obtain ⟨aa, uu⟩ := aa
          simp
          congr
          have := hu _ uu
          rw [Nat.mod_eq]
          have lxs : ¬ 2007 ≤ aa := by exact Nat.not_le_of_lt (hu aa uu)
          simp [this, lxs]
    -- Apply `h` to `s'`
    have h₄ : 1 ≤ s'.card := by
      rw [h₂]
      exact h_card
    have h₅ : ¬(2008 ∣ ∑ i ∈ s', a i) := h s' h₄
    -- Since `∑ i ∈ s', a i = ∑ i ∈ s, a i`, we have `¬(2008 ∣ ∑ i ∈ s, a i)`
    rw [h₃] at h₅
    exact h₅
  exact h_main

lemma holo (a : ℕ → ℕ) (ha : ∀ i, i < 2007 → 1 ≤ a i ∧ a i ≤ 2007) (uh : ∀ i j, i < 2007 → j < 2007 → a i = a j → i = j) (tg : ℕ) (htg : 1 ≤ tg ∧ tg ≤ 2007) : ∃ xx, xx < 2007 ∧ a xx = tg := by
  have alx := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range 2007) (t := Finset.Icc 1 2007) (fun x y => a x) (by { simp; exact ha }) (by { simp; exact uh }) (by simp) tg (by simp; exact htg)
  simp at alx
  obtain ⟨aaa, nbb, xls⟩ := alx
  rw [xls]
  exists aaa

lemma pairwisediff (a : Fin 2007 → ℕ) (ha : ∀ i, 1 ≤ a i ∧ a i < 2008)
    (h : ∀ s : Finset (Fin 2007), 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, a i)) :
  ∀ i j, i < 2007 → j < 2007 → p a i % 2008 = p a j % 2008 → i = j := by
  by_contra! j
  -- we obtain i j, then find subarray with sum = 0
  obtain ⟨i, j, w, e, hh, gg⟩ := j
  wlog ax : i < j
  · have := this a ha h j i e w hh.symm
    simp at ax
    obtain rfl | av := eq_or_lt_of_le ax
    · simp at gg
    have := this (by exact id (Ne.symm gg)) (by assumption)
    exact this
  -- we have generalized
  have := trax _ h (Finset.Ioc (i : ℕ) (j : ℕ)) (by simp; omega)
  rw [p, p] at hh
  have alx := Finset.sum_Ico_eq_sub (m := i + 1) (n := j + 1) (fun x => (a x : ℤ)) (by exact Nat.le_add_right_of_le ax)
  conv at alx => left; norm_cast
  conv at alx => right; left; norm_cast
  apply_fun (fun x => x % 2008) at alx
  rw [Int.sub_emod] at alx
  conv at alx => right; left; left; norm_cast; rw [←hh]
  conv at alx => right; left; right; norm_cast;
  simp at alx
  norm_cast at alx
  -- we have the subarray, now we cause contradiction
  have intax : Finset.Ico (i + 1) (j + 1) = Finset.Ioc i j := by
    ext n
    simp
    clear * -
    omega
  rw [intax] at alx
  simp [alx] at this
  omega

lemma firsttwo (a : Fin 2007 → ℕ) (ha : ∀ i, 1 ≤ a i ∧ a i < 2008)
    (h : ∀ s : Finset (Fin 2007), 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, a i)) :
  a 0 = a 1 := by
  have meme := trax _ h
  clear h
  have xll := holo (fun vv => p a vv % 2008) (by {
    simp [p]
    intros i hi
    constructor
    · have := meme (Finset.range (i + 1)) (by { simp; omega }) (by simp)
      omega
    · omega
  }) (by {
    apply pairwisediff
    · exact ha
    · apply trac
      exact meme
  })
  have lz := xll (a 1) (by {
    have uh := ha 1
    clear * - uh
    omega
  })
  simp at lz
  obtain ⟨xx, hx, vm⟩ := lz
  obtain _ | _ | xx := xx
  -- if xx = 0, contradiction
  · simp [p] at vm
    rw [←vm]
    have mm := ha 0
    omega
  -- if xx = 1
  · simp [p, Finset.sum_range_succ] at vm
    have a1 := ha 0
    have a2 := ha 1
    omega
  -- if xx >= 2, contradiction
  rw [p] at vm
  clear xll
  exfalso
  have dq := meme (Finset.range (xx + 3) \ {1}) (by simp; omega) (by {
    simp
    exists 0
    simp
  })
  zify at dq
  rw [Finset.sum_sdiff_eq_sub (by simp)] at dq
  simp at dq
  conv at dq => right; right; left; norm_cast
  exact dq (by {
    apply Nat.ModEq.dvd
    rw [← vm, Nat.ModEq.eq_1, Nat.mod_mod]
  })

lemma swap (i : Fin 2007) (a b : Fin 2007 → ℕ) (hb : b = fun x => if x = i then a 0 else if x = 0 then a i else a x) (ha : ∀ i, 1 ≤ a i ∧ a i < 2008)
    (h : ∀ s : Finset (Fin 2007), 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, a i)) :
  (∀ i, 1 ≤ b i ∧ b i < 2008) ∧ (∀ s : Finset (Fin 2007), 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, b i)) := by
  have h_bounds : ∀ i, 1 ≤ b i ∧ b i < 2008 := by
    intro j
    rw [hb]
    simp only
    split_ifs with h₁ h₂
    · -- Case: j = i
      have h₃ := ha 0
      have h₄ := ha i
      simp_all [Fin.ext_iff]
    · -- Case: j = 0
      have h₃ := ha i
      have h₄ := ha 0
      simp_all [Fin.ext_iff]

    · -- Case: j ≠ i and j ≠ 0
      have h₃ := ha j
      simp_all [Fin.ext_iff]

  
  have h_sum : ∀ s : Finset (Fin 2007), 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, b i) := by
    intro s h₁
    have h₂ : ¬(2008 ∣ ∑ i ∈ s, b i) := by
      by_cases xx : i = 0
      · simp [hb, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', xx]
        by_cases hh : 0 ∈ s
        all_goals simp [hh]
        (zify; rw [Finset.sum_erase_eq_sub hh]; ring; norm_cast)
        all_goals apply h
        all_goals assumption
      -- now i is not zero
      simp [hb, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', xx, (by exact fun a => xx (id (Eq.symm a)) : ¬0 = i)]
      split_ifs with am xs qq
      all_goals simp [am]
      · zify; rw [Finset.sum_erase_eq_sub (by simp; exact xs), Finset.sum_erase_eq_sub am]
        ring; norm_cast
        apply h; assumption
      · simp [xx] at xs
        have xk := xs (by exact fun a => xx (id (Eq.symm a)))
        have kx := h (s \ {i} ∪ {0}) (by simp)
        simp at kx
        rw [Finset.sum_union (by simp; tauto)] at kx
        simp [xk]
        simp at kx
        rw [Finset.erase_eq, Nat.add_comm]
        exact kx
      · have kx := h (s \ {0} ∪ {i}) (by simp)
        simp at kx
        rw [Finset.sum_union (by simp; tauto)] at kx
        simp at kx
        rw [Finset.erase_eq, Nat.add_comm]
        exact kx
      · simp at qq
        simp [qq (by exact fun a => xx (id (Eq.symm a)))]
        apply h
        exact h₁
    exact h₂
  
  exact ⟨h_bounds, h_sum⟩

/- Je hebt 2007 kaarten. Op elke kaart is een positief geheel getal kleiner dan 2008 geschreven. Als je een aantal (minstens 1) van deze kaarten neemt, is de som van de getallen op de kaarten niet deelbaar door 2008. Bewijs dat op elke kaart hetzelfde getal staat. -/
theorem number_theory_606152 (a : Fin 2007 → ℕ) (ha : ∀ i, 1 ≤ a i ∧ a i < 2008)
    (h : ∀ s : Finset (Fin 2007), 1 ≤ s.card → ¬(2008 ∣ ∑ i ∈ s, a i)) :
    ∃ x, ∀ i, a i = x := by
  exists a 0
  intro i
  obtain ⟨xt, tx⟩ := swap i a (fun x => if x = i then a 0 else if x = 0 then a i else a x) rfl ha h
  have kdx := firsttwo _ xt tx
  by_cases nn : i = 0
  · subst i; rfl
  simp [nn, (by exact fun a => nn (id (Eq.symm a)) : ¬0 = i)] at kdx
  split_ifs at kdx <;> try tauto
  rw [kdx]; symm
  apply firsttwo <;> assumption
