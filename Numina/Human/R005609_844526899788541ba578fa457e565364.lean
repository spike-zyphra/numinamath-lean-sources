import Mathlib

lemma factorization_of_prime_eq_zero_iff {p n : ℕ} (hp : p.Prime) : p.factorization n = 0 ↔ n ≠ p := by
  rw [Nat.factorization_eq_zero_iff]
  constructor
  . rintro (h | h | h)
    . contrapose h
      simp at h ⊢
      rw [h]
      exact hp
    . contrapose h
      simp at h ⊢
      rw [h]
    . contrapose hp
      rw [h]
      decide
  . intro h
    contrapose h
    simp at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    rw [Nat.prime_dvd_prime_iff_eq] at h2
    all_goals assumption

lemma factorization_eq_zero_if_not_prime_factor {n p : ℕ} (hp : p ∉ n.primeFactors): n.factorization p = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  contrapose hp
  simp at hp ⊢
  exact hp

lemma factorization_unique_5_7_11_13 {a b c d a' b' c' d' : ℕ} : 5^a * 7^b * 11^c * 13^d = 5^a' * 7^b' * 11^c' * 13^d' → a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  intro h
  have h_5 := congrArg (fun x => x.factorization 5) h
  have h_7 := congrArg (fun x => x.factorization 7) h
  have h_11 := congrArg (fun x => x.factorization 11) h
  have h_13 := congrArg (fun x => x.factorization 13) h
  simp [Nat.factorization_mul, Nat.factorization_pow] at h_5 h_7 h_11 h_13
  norm_num at h_5 h_7 h_11 h_13
  omega

lemma factorization_subset_primeFactors {n : ℕ} {F : Finset ℕ} (hn : n > 0) (hnF : n.primeFactors ⊆ F) (hF : ∀ p ∈ F, p.Prime): ∏ p ∈ F, p ^ n.factorization p = n := by
  nth_rw 2 [← Nat.factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  symm
  apply Finset.prod_subset hnF
  intro p hp1 hp2
  suffices n.factorization p = 0 by rw [this]; norm_num
  apply Nat.factorization_eq_zero_of_not_dvd
  contrapose hp2
  simp at hp2 ⊢
  exact ⟨hF p hp1, hp2, by omega⟩

lemma factorization_subset_primeFactors_2_3_5_7_11_13 {n : ℕ} (hn : n > 0): n.primeFactors ⊆ {2, 3, 5, 7, 11, 13} → 2 ^ n.factorization 2 * 3 ^ n.factorization 3 * 5 ^ n.factorization 5 * 7 ^ n.factorization 7 * 11 ^ n.factorization 11 * 13 ^ n.factorization 13 = n := by
  intro h
  have := factorization_subset_primeFactors hn h (by simp; decide)
  repeat rw [Finset.prod_insert] at this
  rw [Finset.prod_singleton] at this
  nth_rw 7 [← this]
  ring
  all_goals simp

theorem number_theory_609104 :
  {d : ℕ | d ∣ Nat.factorial 15 ∧ Nat.gcd d 60 = 5}.encard = 36 := by

  let S := {d : ℕ | d ∣ Nat.factorial 15 ∧ Nat.gcd d 60 = 5}
  let T1 := {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | 1 ≤ a ∧ a ≤ 3 ∧ b ≤ 2 ∧ c ≤ 1 ∧ d ≤ 1}

  let Tf1 := (Finset.Icc 1 3) ×ˢ (Finset.Icc 0 2) ×ˢ (Finset.Icc 0 1) ×ˢ (Finset.Icc 0 1)

  have hT1 : T1.encard = 36 := by
    have : T1 = Tf1 := by
      ext ⟨a, b, c, d⟩
      simp
      unfold T1 Tf1
      simp
      omega

    rw [this]
    norm_cast

  let f1 : (ℕ × ℕ × ℕ × ℕ) → ℕ := fun (a, b, c, d) => 5^a * 7^b * 11^c * 13^d

  have hf1 : Set.InjOn f1 T1 := by
    unfold Set.InjOn f1
    intro ⟨a,b,c,d⟩ h1 ⟨a',b',c',d'⟩ h2 heq
    simp at heq
    apply factorization_unique_5_7_11_13 at heq
    obtain ⟨heq1, heq2, heq3, heq4⟩ := heq
    subst a b c d
    rfl

  have : Nat.factorial 15 ≠ 0 := by decide
  have h1 : f1 '' T1 = S := by
    unfold f1 T1 Set.image S
    ext x
    simp
    constructor
    . rintro ⟨a,b,c,d, ⟨h1, h2, h3, h4, h5⟩, h6⟩
      have : x ≠ 0 := by
        by_contra h
        rw [h] at h6
        simp at h6

      have : x.gcd 60 ≠ 0 := by
        by_contra h
        rw [Nat.gcd_eq_zero_iff] at h
        omega
      have : 5 ^ a ≠ 0 := by simp
      have : 7 ^ b ≠ 0 := by simp
      have : 11 ^ c ≠ 0 := by simp
      have : 13 ^ d ≠ 0 := by simp
      have : 5 ^ a * 7 ^ b ≠ 0 := by simp
      have : 5 ^ a * 7 ^ b * 11 ^ c ≠ 0 := by simp

      have ha : a = x.factorization 5 := by
        rw [← h6]
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        simp
        rw [show (Nat.factorization 5) 5 = 1 by native_decide]
        rw [show (Nat.factorization 7) 5 = 0 by native_decide]
        rw [show (Nat.factorization 11) 5 = 0 by native_decide]
        rw [show (Nat.factorization 13) 5 = 0 by native_decide]
        simp
        all_goals omega

      have hb : b = x.factorization 7 := by
        rw [← h6]
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        simp
        rw [show (Nat.factorization 5) 7 = 0 by native_decide]
        rw [show (Nat.factorization 7) 7 = 1 by native_decide]
        rw [show (Nat.factorization 11) 7 = 0 by native_decide]
        rw [show (Nat.factorization 13) 7 = 0 by native_decide]
        simp
        all_goals omega

      have hc : c = x.factorization 11 := by
        rw [← h6]
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        simp
        rw [show (Nat.factorization 5) 11 = 0 by native_decide]
        rw [show (Nat.factorization 7) 11 = 0 by native_decide]
        rw [show (Nat.factorization 11) 11 = 1 by native_decide]
        rw [show (Nat.factorization 13) 11 = 0 by native_decide]
        simp
        all_goals omega

      have hd : d = x.factorization 13 := by
        rw [← h6]
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        simp
        rw [show (Nat.factorization 5) 13 = 0 by native_decide]
        rw [show (Nat.factorization 7) 13 = 0 by native_decide]
        rw [show (Nat.factorization 11) 13 = 0 by native_decide]
        rw [show (Nat.factorization 13) 13 = 1 by native_decide]
        simp
        all_goals omega


      refine ⟨?_, ?_⟩
      . rw [← Nat.factorization_le_iff_dvd (by assumption) (by assumption)]
        intro p
        by_cases hp1 : p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ)
        . simp at hp1
          rcases hp1 with rfl | rfl | rfl | rfl | rfl | rfl
          . suffices x.factorization 2 = 0 by rw [this]; omega
            rw [← h6]
            repeat rw [Nat.factorization_mul]
            repeat rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 5) 2 = 0 by native_decide]
            rw [show (Nat.factorization 7) 2 = 0 by native_decide]
            rw [show (Nat.factorization 11) 2 = 0 by native_decide]
            rw [show (Nat.factorization 13) 2 = 0 by native_decide]
            simp
            all_goals omega

          . suffices x.factorization 3 = 0 by rw [this]; omega
            rw [← h6]
            repeat rw [Nat.factorization_mul]
            repeat rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 5) 3 = 0 by native_decide]
            rw [show (Nat.factorization 7) 3 = 0 by native_decide]
            rw [show (Nat.factorization 11) 3 = 0 by native_decide]
            rw [show (Nat.factorization 13) 3 = 0 by native_decide]
            simp
            all_goals omega

          . rw [show (Nat.factorial 15).factorization 5 = 3 by native_decide]
            rw [← ha]
            assumption

          . rw [show (Nat.factorial 15).factorization 7 = 2 by native_decide]
            rw [← hb]
            assumption

          . rw [show (Nat.factorial 15).factorization 11 = 1 by native_decide]
            rw [← hc]
            assumption

          . rw [show (Nat.factorial 15).factorization 13 = 1 by native_decide]
            rw [← hd]
            assumption

        . suffices x.factorization p = 0 by rw [this]; omega
          rw [← h6]
          repeat rw [Nat.factorization_mul]
          repeat rw [Nat.factorization_pow]
          simp
          all_goals try omega
          refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
          all_goals right; rw [factorization_of_prime_eq_zero_iff (by norm_num)]; simp at hp1; omega

      . apply Nat.eq_of_factorization_eq (by assumption) (by norm_num)
        intro p
        rw [Nat.factorization_gcd]
        simp
        by_cases hp : p = 5
        . rw [hp]
          rw [show Nat.factorization 5 5 = 1 by native_decide]
          rw [show Nat.factorization 60 5 = 1 by native_decide]
          simp
          rw [← ha]
          assumption

        . have := @factorization_of_prime_eq_zero_iff 5 p (by norm_num)
          push_neg at hp
          rw [this.mpr hp]
          simp
          by_cases hp1 : p = 2 ∨ p = 3
          . left
            rcases hp1 with rfl | rfl
            . rw [← h6]
              repeat rw [Nat.factorization_mul]
              repeat rw [Nat.factorization_pow]
              simp
              rw [show (Nat.factorization 5) 2 = 0 by native_decide]
              rw [show (Nat.factorization 7) 2 = 0 by native_decide]
              rw [show (Nat.factorization 11) 2 = 0 by native_decide]
              rw [show (Nat.factorization 13) 2 = 0 by native_decide]
              simp
              all_goals omega
            . rw [← h6]
              repeat rw [Nat.factorization_mul]
              repeat rw [Nat.factorization_pow]
              simp
              rw [show (Nat.factorization 5) 3 = 0 by native_decide]
              rw [show (Nat.factorization 7) 3 = 0 by native_decide]
              rw [show (Nat.factorization 11) 3 = 0 by native_decide]
              rw [show (Nat.factorization 13) 3 = 0 by native_decide]
              simp
              all_goals omega

          . right
            apply factorization_eq_zero_if_not_prime_factor
            rw [show Nat.primeFactors 60 = {2, 3, 5} by native_decide]
            simp
            omega

        all_goals omega
    . intro ⟨h1, h2⟩

      have : x ≠ 0 := by
        by_contra h
        rw [h] at h2
        simp at h2

      have : Nat.factorial 15 ≠ 0 := by decide

      have : x.factorization 2 = 0 := by
        apply congrArg (fun x => x.factorization 2) at h2
        rw [Nat.factorization_gcd] at h2
        rw [show Nat.factorization 5 2 = 0 by native_decide] at h2
        simp at h2
        rw [show Nat.factorization 60 2 = 2 by native_decide] at h2
        simp at h2
        all_goals omega
      have : x.factorization 3 = 0 := by
        apply congrArg (fun x => x.factorization 3) at h2
        rw [Nat.factorization_gcd] at h2
        rw [show Nat.factorization 5 3 = 0 by native_decide] at h2
        simp at h2
        rw [show Nat.factorization 60 3 = 1 by native_decide] at h2
        simp at h2
        all_goals omega

      use x.factorization 5, x.factorization 7, x.factorization 11, x.factorization 13
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      . apply congrArg (fun x => x.factorization 5) at h2
        rw [Nat.factorization_gcd] at h2
        rw [show Nat.factorization 5 5 = 1 by native_decide] at h2
        simp at h2
        rw [show Nat.factorization 60 5 = 1 by native_decide] at h2
        simp at h2
        all_goals omega
      . rw [← Nat.factorization_le_iff_dvd] at h1
        have := h1 5
        rw [show (Nat.factorial 15).factorization 5 = 3 by native_decide] at this
        all_goals try omega
      . rw [← Nat.factorization_le_iff_dvd] at h1
        have := h1 7
        rw [show (Nat.factorial 15).factorization 7 = 2 by native_decide] at this
        all_goals try omega
      . rw [← Nat.factorization_le_iff_dvd] at h1
        have := h1 11
        rw [show (Nat.factorial 15).factorization 11 = 1 by native_decide] at this
        all_goals try omega
      . rw [← Nat.factorization_le_iff_dvd] at h1
        have := h1 13
        rw [show (Nat.factorial 15).factorization 13 = 1 by native_decide] at this
        all_goals try omega
      . have := Nat.primeFactors_mono h1 (by assumption)
        rw [show (Nat.factorial 15).primeFactors = {2, 3, 5, 7, 11, 13} by native_decide] at this

        have := @factorization_subset_primeFactors_2_3_5_7_11_13 x (by omega) this
        nth_rw 5 [← this]
        rw [show x.factorization 2 = 0 by assumption]
        rw [show x.factorization 3 = 0 by assumption]
        simp

  have h3 := Set.InjOn.encard_image hf1
  rw [h1, hT1] at h3
  exact h3
