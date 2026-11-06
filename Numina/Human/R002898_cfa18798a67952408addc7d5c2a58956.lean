import Mathlib

lemma max_eq_n_encard (n : ℕ) (hn : n ∈ ({1, 2, 3, 4}: Set ℕ)): {(x, y) : ℕ × ℕ | max x y = n}.encard = 2 * n + 1 := by
  have h1 : {(x, y) : ℕ × ℕ | max x y = n} = (Finset.Icc 0 n ×ˢ {n}) ∪ ({n} ×ˢ Finset.Icc 0 n) := by
    ext ⟨x, y⟩ 
    simp 
    rw [max_def]
    split_ifs
    . constructor
      . intro h
        subst y
        simp; left; assumption
      . rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        . omega
        . omega
    . omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  simp at hn
  rcases hn with rfl | rfl | rfl | rfl
  all_goals simp; decide


lemma factorization_prod_pow_eq_self {n : ℕ} (hn: n ≠ 0):
  n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rfl

lemma factorization_unique {a b c d a' b' c' d': ℕ} : 2^a * 3^b * 7^c * 11^d = 2^a' * 3^b' * 7^c' * 11^d' → a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  intro h
  refine ⟨?_, ?_, ?_, ?_⟩
  . apply congrArg (fun x => x.factorization 2) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 2 = 1 by norm_num] at h
    rw [show (Nat.factorization 3) 2 = 0 by norm_num] at h
    rw [show (Nat.factorization 7) 2 = 0 by norm_num] at h
    rw [show (Nat.factorization 11) 2 = 0 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 3) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 3 = 0 by norm_num] at h
    rw [show (Nat.factorization 3) 3 = 1 by norm_num] at h
    rw [show (Nat.factorization 7) 3 = 0 by norm_num] at h
    rw [show (Nat.factorization 11) 3 = 0 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 7) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 7 = 0 by norm_num] at h
    rw [show (Nat.factorization 3) 7 = 0 by norm_num] at h
    rw [show (Nat.factorization 7) 7 = 1 by norm_num] at h
    rw [show (Nat.factorization 11) 7 = 0 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 11) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 11 = 0 by norm_num] at h
    rw [show (Nat.factorization 3) 11 = 0 by norm_num] at h
    rw [show (Nat.factorization 7) 11 = 0 by norm_num] at h
    rw [show (Nat.factorization 11) 11 = 1 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h


lemma factorization_subset_primeFactors {n : ℕ} (hn : n > 0): n.primeFactors ⊆ {2, 3, 7, 11} → 2 ^ n.factorization 2 * 3 ^ n.factorization 3 * 7 ^ n.factorization 7 * 11 ^ n.factorization 11 = n := by
  intro h
  nth_rw 5 [factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
  have h_zero : ∀ p ∈ ({2, 3, 7, 11}: Finset ℕ), p ∉ n.primeFactors → p ^ n.factorization p = 1 := by
    intro p hp1 hp2
    suffices n.factorization p = 0 by
      rw [this]
      norm_num

    apply Nat.factorization_eq_zero_of_not_dvd
    contrapose hp2
    simp
    simp at hp2
    refine ⟨?_, hp2, by omega⟩
    simp at hp1
    rcases hp1 with rfl | rfl | rfl | rfl
    all_goals norm_num

  rw [Finset.prod_subset h h_zero]
  simp
  ring

theorem number_theory_127733 :
  {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a.lcm b = 232848}.encard = 945 := by


  let S := {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a.lcm b = 232848}
  let T1 := {(x, y) : ℕ × ℕ | max x y = 4}
  let T2 := {(x, y) : ℕ × ℕ | max x y = 3}
  let T3 := {(x, y) : ℕ × ℕ | max x y = 2}
  let T4 := {(x, y) : ℕ × ℕ | max x y = 1}
  let f1 : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) → (ℕ × ℕ) := fun ⟨(x1, y1), (x2, y2), (x3, y3), (x4, y4)⟩ => (2^x1 * 3^x2 * 7^x3 * 11^x4, 2^y1 * 3^y2 * 7^y3 * 11^y4)

  have hf1 : Set.InjOn f1 (T1 ×ˢ T2 ×ˢ T3 ×ˢ T4) := by
    unfold Set.InjOn f1
    intro ⟨⟨x1,y1⟩, ⟨x2,y2⟩, ⟨x3,y3⟩, ⟨x4,y4⟩⟩ ⟨h1, h2, h3, h4⟩ ⟨⟨x1',y1'⟩, ⟨x2',y2'⟩, ⟨x3',y3'⟩, ⟨x4',y4'⟩⟩ ⟨h1', h2', h3', h4'⟩ hxy
    simp only [Set.mem_prod, Prod.mk.injEq] at h1 h2 h3 h4 h1' h2' h3' h4' hxy
    obtain ⟨hx, hy⟩ := hxy
    apply factorization_unique at hx
    apply factorization_unique at hy

    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
    
    subst x1 x2 x3 x4 y1 y2 y3 y4
    rfl


  have h1 : f1 '' (T1 ×ˢ T2 ×ˢ T3 ×ˢ T4) = S := by
    unfold f1 T1 T2 T3 T4 Set.image S
    ext ⟨x, y⟩
    simp
    constructor
    . rintro ⟨a, b, c, d, e, f, g, h, ⟨h1, h2, h3, h4⟩, h5, h6⟩
      rw [← h5, ← h6]
      simp
      apply Nat.eq_of_factorization_eq
      . apply Nat.lcm_ne_zero
        . simp
        . simp

      . norm_num
      . intro p
        by_cases hp_prime : Nat.Prime p
        . rw [Nat.factorization_lcm (by simp) (by simp), Finsupp.sup_apply]
          by_cases hp: p = 2 ∨ p = 3 ∨ p = 7 ∨ p = 11
          . rcases hp with rfl | rfl | rfl | rfl
            . rw [show (Nat.factorization 232848) 2 = 4 by native_decide]
              repeat rw [Nat.factorization_mul, Finsupp.add_apply]
              repeat rw [Nat.factorization_pow]
              simp
              rw [show (Nat.factorization 2) 2 = 1 by norm_num]
              rw [show (Nat.factorization 3) 2 = 0 by norm_num]
              rw [show (Nat.factorization 7) 2 = 0 by norm_num]
              rw [show (Nat.factorization 11) 2 = 0 by norm_num]
              simp; exact h1
              all_goals by_contra h; simp at h
            . rw [show (Nat.factorization 232848) 3 = 3 by native_decide]
              repeat rw [Nat.factorization_mul, Finsupp.add_apply]
              repeat rw [Nat.factorization_pow]
              simp
              rw [show (Nat.factorization 2) 3 = 0 by norm_num]
              rw [show (Nat.factorization 3) 3 = 1 by norm_num]
              rw [show (Nat.factorization 7) 3 = 0 by norm_num]
              rw [show (Nat.factorization 11) 3 = 0 by norm_num]
              simp; exact h2
              all_goals by_contra h; simp at h
            . rw [show (Nat.factorization 232848) 7 = 2 by native_decide]
              repeat rw [Nat.factorization_mul, Finsupp.add_apply]
              repeat rw [Nat.factorization_pow]
              simp
              rw [show (Nat.factorization 2) 7 = 0 by norm_num]
              rw [show (Nat.factorization 3) 7 = 0 by norm_num]
              rw [show (Nat.factorization 7) 7 = 1 by norm_num]
              rw [show (Nat.factorization 11) 7 = 0 by norm_num]
              simp; exact h3
              all_goals by_contra h; simp at h
            . rw [show (Nat.factorization 232848) 11 = 1 by native_decide]
              repeat rw [Nat.factorization_mul, Finsupp.add_apply]
              repeat rw [Nat.factorization_pow]
              simp
              rw [show (Nat.factorization 2) 11 = 0 by norm_num]
              rw [show (Nat.factorization 3) 11 = 0 by norm_num]
              rw [show (Nat.factorization 7) 11 = 0 by norm_num]
              rw [show (Nat.factorization 11) 11 = 1 by norm_num]
              simp; exact h4
              all_goals by_contra h; simp at h
          . simp at hp
            obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
            rw [show Nat.factorization 232848 p = 0 by
              rw [Nat.factorization_eq_zero_iff]
              right; left
              by_contra h_contra
              have : p ∈ Nat.primeFactors 232848 := by
                simp
                exact ⟨hp_prime, h_contra⟩
              rw [(show Nat.primeFactors 232848 = ({2, 3, 7, 11}: Finset ℕ) by native_decide)] at this
              simp at this
              omega
            ]
            simp
            refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
            all_goals right; norm_num; rw [Finsupp.single_apply]; simp; omega

        . rw [Nat.factorization_eq_zero_of_non_prime 232848 hp_prime]
          apply Nat.factorization_eq_zero_of_non_prime
          exact hp_prime
      
    . intro ⟨hx1, hx2, hx3⟩
      use x.factorization 2,  y.factorization 2
      use x.factorization 3,  y.factorization 3
      use x.factorization 7,  y.factorization 7
      use x.factorization 11,  y.factorization 11
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      . have := congr_arg (fun x => x.factorization 2) hx3
        simp at this
        rw [show Nat.factorization 232848 2 = 4 by native_decide] at this
        rw [Nat.factorization_lcm, Finsupp.sup_apply] at this
        exact this
        all_goals omega
      . have := congr_arg (fun x => x.factorization 3) hx3
        simp at this
        rw [show Nat.factorization 232848 3 = 3 by native_decide] at this
        rw [Nat.factorization_lcm, Finsupp.sup_apply] at this
        exact this
        all_goals omega
      . have := congr_arg (fun x => x.factorization 7) hx3
        simp at this
        rw [show Nat.factorization 232848 7 = 2 by native_decide] at this
        rw [Nat.factorization_lcm, Finsupp.sup_apply] at this
        exact this
        all_goals omega
      . have := congr_arg (fun x => x.factorization 11) hx3
        simp at this
        rw [show Nat.factorization 232848 11 = 1 by native_decide] at this
        rw [Nat.factorization_lcm, Finsupp.sup_apply] at this
        exact this
        all_goals omega
      . apply factorization_subset_primeFactors
        . omega
        . intro p hp
          simp at hp
          obtain ⟨hp1, hp2, hp3⟩ := hp
          have : x ∣ x.lcm y := dvd_lcm_left x y
          rw [hx3] at this
          have : p ∣ 232848 := by
            apply Nat.dvd_trans hp2
            exact this
          rw [← (show Nat.primeFactors 232848 = ({2, 3, 7, 11}: Finset ℕ) by native_decide)]
          simp
          exact ⟨hp1, this⟩

      . apply factorization_subset_primeFactors
        . omega
        . intro p hp
          simp at hp
          obtain ⟨hp1, hp2, hp3⟩ := hp
          have : y ∣ x.lcm y := dvd_lcm_right x y
          rw [hx3] at this
          have : p ∣ 232848 := by
            apply Nat.dvd_trans hp2
            exact this

          rw [← (show Nat.primeFactors 232848 = ({2, 3, 7, 11}: Finset ℕ) by native_decide)]
          simp
          exact ⟨hp1, this⟩

  
  have h2 : (T1 ×ˢ T2 ×ˢ T3 ×ˢ T4).encard = 945 := by
    have hT1_encard : T1.encard = 9 := max_eq_n_encard 4 (by simp)
    have hT2_encard : T2.encard = 7 := max_eq_n_encard 3 (by simp)
    have hT3_encard : T3.encard = 5 := max_eq_n_encard 2 (by simp)
    have hT4_encard : T4.encard = 3 := max_eq_n_encard 1 (by simp)
    
    have hT1_finite: T1.encard < ⊤ := by rw [hT1_encard]; decide
    have hT2_finite: T2.encard < ⊤ := by rw [hT2_encard]; decide
    have hT3_finite: T3.encard < ⊤ := by rw [hT3_encard]; decide
    have hT4_finite: T4.encard < ⊤ := by rw [hT4_encard]; decide
    simp at hT1_finite hT2_finite hT3_finite hT4_finite

    have hT1_encard': hT1_finite.toFinset.card = 9 := by rw [Set.Finite.encard_eq_coe_toFinset_card hT1_finite] at hT1_encard; norm_cast at hT1_encard
    have hT2_encard': hT2_finite.toFinset.card = 7 := by rw [Set.Finite.encard_eq_coe_toFinset_card hT2_finite] at hT2_encard; norm_cast at hT2_encard
    have hT3_encard': hT3_finite.toFinset.card = 5 := by rw [Set.Finite.encard_eq_coe_toFinset_card hT3_finite] at hT3_encard; norm_cast at hT3_encard
    have hT4_encard': hT4_finite.toFinset.card = 3 := by rw [Set.Finite.encard_eq_coe_toFinset_card hT4_finite] at hT4_encard; norm_cast at hT4_encard

    have hT_finite: (T1 ×ˢ T2 ×ˢ T3 ×ˢ T4).Finite := by
      have := Set.Finite.prod hT3_finite hT4_finite
      have := Set.Finite.prod hT2_finite this
      have := Set.Finite.prod hT1_finite this
      exact this

    rw [Set.Finite.encard_eq_coe_toFinset_card hT_finite]
    norm_cast

    have h_eq : hT_finite.toFinset = hT1_finite.toFinset ×ˢ hT2_finite.toFinset ×ˢ hT3_finite.toFinset ×ˢ hT4_finite.toFinset := by
      repeat rw [← Set.Finite.toFinset_prod]

    rw [h_eq]
    repeat rw [Finset.card_product]
    rw [hT1_encard', hT2_encard', hT3_encard', hT4_encard']

  have h3 := Set.InjOn.encard_image hf1
  rw [h1, h2] at h3
  exact h3
