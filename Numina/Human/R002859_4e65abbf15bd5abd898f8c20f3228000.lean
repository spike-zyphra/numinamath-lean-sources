import Mathlib

/- # Problem:
 1.1. How many solutions in natural numbers does the equation $\operatorname{LCM}(n, k)=2^{3} 3^{5} 5^{7}$ have?
1.1. Если $n=2^{a} 3^{b} 5^{c}, k=2^{A} 3^{B} 5^{C}$, то пара $(a, A)$ может принимать 7 значений (одно из чисел 3 , второе от 0 до 3 ), пара $(b, B)-11$ значений, $(c, C)-15$ значений. Таким образом, ответ $7 \cdot 11 \cdot 15=1155$. -/

lemma max_eq_n_encard (n : ℕ) (hn : n ∈ ({1, 2, 3, 4, 5, 6, 7}: Set ℕ)): {(x, y) : ℕ × ℕ | max x y = n}.encard = 2 * n + 1 := by
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
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp; decide


lemma factorization_prod_pow_eq_self {n : ℕ} (hn: n ≠ 0):
  n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rfl

lemma factorization_unique_2_3_5 {a b c a' b' c' : ℕ} : 2^a * 3^b * 5^c = 2^a' * 3^b' * 5^c' → a = a' ∧ b = b' ∧ c = c' := by
  intro h
  refine ⟨?_, ?_, ?_⟩
  . apply congrArg (fun x => x.factorization 2) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 2 = 1 by norm_num] at h
    rw [show (Nat.factorization 3) 2 = 0 by norm_num] at h
    rw [show (Nat.factorization 5) 2 = 0 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 3) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 3 = 0 by norm_num] at h
    rw [show (Nat.factorization 3) 3 = 1 by norm_num] at h
    rw [show (Nat.factorization 5) 3 = 0 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h
  . apply congrArg (fun x => x.factorization 5) at h
    repeat rw [Nat.factorization_mul, Finsupp.add_apply] at h
    repeat rw [Nat.factorization_pow] at h
    simp at h
    rw [show (Nat.factorization 2) 5 = 0 by norm_num] at h
    rw [show (Nat.factorization 3) 5 = 0 by norm_num] at h
    rw [show (Nat.factorization 5) 5 = 1 by norm_num] at h
    simp at h
    exact h
    all_goals by_contra h; simp at h


lemma factorization_subset_primeFactors {n : ℕ} (hn : n > 0): n.primeFactors ⊆ {2, 3, 5} → 2 ^ n.factorization 2 * 3 ^ n.factorization 3 * 5 ^ n.factorization 5 = n := by
  intro h
  nth_rw 4 [factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
  have h_zero : ∀ p ∈ ({2, 3, 5}: Finset ℕ), p ∉ n.primeFactors → p ^ n.factorization p = 1 := by
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


theorem number_theory_123016 :
    {(n, k) : ℕ × ℕ | Nat.lcm n k = 2^3 * 3^5 * 5^7}.encard = 1155 := by


  let S := {(n, k) : ℕ × ℕ | Nat.lcm n k = 2^3 * 3^5 * 5^7}
  let T1 := {(x, y) : ℕ × ℕ | max x y = 3}
  let T2 := {(x, y) : ℕ × ℕ | max x y = 5}
  let T3 := {(x, y) : ℕ × ℕ | max x y = 7}
  let f1 : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) → (ℕ × ℕ) := fun ⟨(x1, y1), (x2, y2), (x3, y3)⟩ => (2^x1 * 3^x2 * 5^x3, 2^y1 * 3^y2 * 5^y3)

  have hf1 : Set.InjOn f1 (T1 ×ˢ T2 ×ˢ T3) := by
    unfold Set.InjOn f1
    intro ⟨⟨x1,y1⟩, ⟨x2,y2⟩, ⟨x3,y3⟩⟩ ⟨h1, h2, h3⟩ ⟨⟨x1',y1'⟩, ⟨x2',y2'⟩, ⟨x3',y3'⟩⟩ ⟨h1', h2', h3'⟩ hxy
    simp only [Set.mem_prod, Prod.mk.injEq] at h1 h2 h3 h1' h2' h3' hxy
    obtain ⟨hx, hy⟩ := hxy
    apply factorization_unique_2_3_5 at hx
    apply factorization_unique_2_3_5 at hy

    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy

    subst x1 x2 x3 y1 y2 y3
    rfl


  have h1 : f1 '' (T1 ×ˢ T2 ×ˢ T3) = S := by
    unfold f1 T1 T2 T3 Set.image S
    ext ⟨x, y⟩
    simp
    constructor
    . rintro ⟨a, b, c, d, e, f, ⟨h1, h2, h3⟩, h5, h6⟩
      rw [← h5, ← h6]
      apply Nat.eq_of_factorization_eq
      . apply Nat.lcm_ne_zero
        . simp
        . simp
      . norm_num
      . intro p
        by_cases hp_prime : p ∈ ({2, 3, 5}: Finset ℕ)
        . simp at hp_prime
          rcases hp_prime with rfl | rfl | rfl
          . rw [show (Nat.factorization 151875000) 2 = 3 by native_decide]
            rw [Nat.factorization_lcm]
            repeat rw [Nat.factorization_mul]
            repeat rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 2) 2 = 1 by norm_num]
            rw [show (Nat.factorization 3) 2 = 0 by norm_num]
            rw [show (Nat.factorization 5) 2 = 0 by norm_num]
            simp
            exact h1
            all_goals by_contra h; simp at h
          . rw [show (Nat.factorization 151875000) 3 = 5 by native_decide]
            rw [Nat.factorization_lcm]
            repeat rw [Nat.factorization_mul]
            repeat rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 2) 3 = 0 by norm_num]
            rw [show (Nat.factorization 3) 3 = 1 by norm_num]
            rw [show (Nat.factorization 5) 3 = 0 by norm_num]
            simp
            exact h2
            all_goals by_contra h; simp at h
          . rw [show (Nat.factorization 151875000) 5 = 7 by native_decide]
            rw [Nat.factorization_lcm]
            repeat rw [Nat.factorization_mul]
            repeat rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 2) 5 = 0 by norm_num]
            rw [show (Nat.factorization 3) 5 = 0 by norm_num]
            rw [show (Nat.factorization 5) 5 = 1 by norm_num]
            simp
            exact h3
            all_goals by_contra h; simp at h
        . rw [show 151875000 = 2^3 * 3^5 * 5^7 by norm_num]
          rw [Nat.factorization_lcm]
          repeat rw [Nat.factorization_mul]
          repeat rw [Nat.factorization_pow]
          simp
          rw [show (Nat.factorization 2) p = 0 by
            rw [Nat.factorization_eq_zero_iff]
            by_contra h
            simp at h
            obtain ⟨hp1, hp2⟩ := h
            apply Nat.le_of_dvd (by norm_num) at hp2
            interval_cases p
            . contrapose hp1; decide
            . contrapose hp1; decide
            . simp at hp_prime
          ]
          rw [show (Nat.factorization 3) p = 0 by
            rw [Nat.factorization_eq_zero_iff]
            by_contra h
            simp at h
            obtain ⟨hp1, hp2⟩ := h
            apply Nat.le_of_dvd (by norm_num) at hp2
            interval_cases p
            all_goals contrapose hp1; try decide
            all_goals simp at hp_prime
          ]
          rw [show (Nat.factorization 5) p = 0 by
            rw [Nat.factorization_eq_zero_iff]
            by_contra h
            simp at h
            obtain ⟨hp1, hp2⟩ := h
            apply Nat.le_of_dvd (by norm_num) at hp2
            interval_cases p
            all_goals contrapose hp1; try decide
            all_goals simp at hp_prime
          ]
          all_goals simp
    . intro hx1
      have : x ≠ 0 := by
        by_contra h
        rw [h] at hx1
        simp at hx1
      have : y ≠ 0 := by
        by_contra h
        rw [h] at hx1
        simp at hx1
      use x.factorization 2,  y.factorization 2,  x.factorization 3,  y.factorization 3,  x.factorization 5,  y.factorization 5
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      . have := congr_arg (fun x => x.factorization 2) hx1
        simp at this
        rw [Nat.factorization_lcm] at this
        rw [show (Nat.factorization 151875000) 2 = 3 by native_decide] at this
        simp at this
        exact this
        all_goals assumption
      . have := congr_arg (fun x => x.factorization 3) hx1
        simp at this
        rw [Nat.factorization_lcm] at this
        rw [show (Nat.factorization 151875000) 3 = 5 by native_decide] at this
        simp at this
        exact this
        all_goals assumption
      . have := congr_arg (fun x => x.factorization 5) hx1
        simp at this
        rw [Nat.factorization_lcm] at this
        rw [show (Nat.factorization 151875000) 5 = 7 by native_decide] at this
        simp at this
        exact this
        all_goals assumption
      . apply factorization_subset_primeFactors
        . omega
        . intro p hp
          simp at hp
          obtain ⟨hp1, hp2, hp3⟩ := hp
          have := Nat.dvd_lcm_left x y
          rw [hx1] at this
          have := Nat.dvd_trans hp2 this
          have : p ∈ Nat.primeFactors 151875000 := by
            simp
            exact ⟨hp1, this⟩
          rw [show Nat.primeFactors 151875000= {2,3,5} by native_decide] at this
          exact this
      . apply factorization_subset_primeFactors
        . omega
        . intro p hp
          simp at hp
          obtain ⟨hp1, hp2, hp3⟩ := hp
          have := Nat.dvd_lcm_right x y
          rw [hx1] at this
          have := Nat.dvd_trans hp2 this
          have : p ∈ Nat.primeFactors 151875000 := by
            simp
            exact ⟨hp1, this⟩
          rw [show Nat.primeFactors 151875000= {2,3,5} by native_decide] at this
          exact this


  have h2 : (T1 ×ˢ T2 ×ˢ T3).encard = 1155 := by
    have hT1_encard : T1.encard = 7 := max_eq_n_encard 3 (by simp)
    have hT2_encard : T2.encard = 11 := max_eq_n_encard 5 (by simp)
    have hT3_encard : T3.encard = 15 := max_eq_n_encard 7 (by simp)

    have hT1_finite: T1.encard < ⊤ := by rw [hT1_encard]; decide
    have hT2_finite: T2.encard < ⊤ := by rw [hT2_encard]; decide
    have hT3_finite: T3.encard < ⊤ := by rw [hT3_encard]; decide
    simp at hT1_finite hT2_finite hT3_finite

    have hT1_encard': hT1_finite.toFinset.card = 7 := by rw [Set.Finite.encard_eq_coe_toFinset_card hT1_finite] at hT1_encard; norm_cast at hT1_encard
    have hT2_encard': hT2_finite.toFinset.card = 11 := by rw [Set.Finite.encard_eq_coe_toFinset_card hT2_finite] at hT2_encard; norm_cast at hT2_encard
    have hT3_encard': hT3_finite.toFinset.card = 15 := by rw [Set.Finite.encard_eq_coe_toFinset_card hT3_finite] at hT3_encard; norm_cast at hT3_encard

    have hT_finite: (T1 ×ˢ T2 ×ˢ T3).Finite := by
      have := Set.Finite.prod hT2_finite hT3_finite
      have := Set.Finite.prod hT1_finite this
      exact this

    rw [Set.Finite.encard_eq_coe_toFinset_card hT_finite]
    norm_cast

    have h_eq : hT_finite.toFinset = hT1_finite.toFinset ×ˢ hT2_finite.toFinset ×ˢ hT3_finite.toFinset := by
      repeat rw [← Set.Finite.toFinset_prod]

    rw [h_eq]
    repeat rw [Finset.card_product]
    rw [hT1_encard', hT2_encard', hT3_encard']

  have h3 := Set.InjOn.encard_image hf1
  rw [h1, h2] at h3
  exact h3
