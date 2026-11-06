import Mathlib

set_option linter.constructorNameAsVariable false

/- # Problem:
 1. How many divisors of the number $30^{2008}$ are not divisors of the number $20^{2007}$?
Решение. Бидејќи $30^{2008}=2^{2008} \cdot 3^{2008} \cdot 5^{2008}$ и $20^{2007}=2^{4014} \cdot 5^{2007}$, тогаш сите делители на $30^{2008}$ кои не се делители на $20^{2007}$ се од вид:

1. $2^{k} \cdot 3^{l} \cdot 5^{m}, l=1, \ldots, 2008, k, m=0,1, \ldots, 2008$ и нив ги има вкупно $2008 \cdot 2009^{2}$ или од вид:
2. $2^{k} \cdot 5^{m}, m=2008, k=0,1,2, \ldots, 2008$ и нив ги има $1 \cdot 2009=2009$.

Значи, има вкупно $2008 \cdot 2009^{2}+2009$ делители на бројот $30^{2008}$ не се делители на бројот $20^{2007}$. -/

lemma factorization_unique_2_3_5 {a b c d e f : ℕ} : 2^a * 3^b * 5^c = 2^d * 3^e * 5^f → a = d ∧ b = e ∧ c = f := by
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

lemma prime_factor_of_dvd_n_pow_eq_n_prime_factor {n x m : ℕ} (hn : 0 < n) (h: x ∣ n ^ m): x.primeFactors ⊆ n.primeFactors := by
  intro p hp
  simp at hp
  simp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  . exact hp1
  . apply @Nat.Prime.dvd_of_dvd_pow p n m
    . exact hp1
    . exact Nat.dvd_trans hp2 h
  . omega

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

theorem number_theory_214458 :
    {x | x ∣ 30^2008 ∧ ¬x ∣ 20^2007}.encard = 2008 * 2009^2 + 2009 := by


  let S := {x | x ∣ 30^2008 ∧ ¬x ∣ 20^2007}
  let T1 := Finset.filter (fun ⟨u, v, w⟩ => (0 < v ∨ w = 2008))
    (Finset.Icc 0 2008 ×ˢ Finset.Icc 0 2008 ×ˢ Finset.Icc 0 2008)

  let T2 := Finset.Icc 0 2008 ×ˢ Finset.Icc 1 2008 ×ˢ Finset.Icc 0 2008

  let T3 := Finset.Icc 0 2008 ×ˢ {0} ×ˢ {2008}

  have h_T1_eq_T2_T3: T1 = T2 ∪ T3 := by
    unfold T1 T2 T3
    ext ⟨a, b, c⟩
    simp
    constructor
    . rintro ⟨⟨h1, h2, h3⟩, h4⟩
      rcases h4 with h4 | h4
      . left; omega
      . rw [h4]; simp
        by_cases hb : 1 ≤ b
        . omega
        . simp at hb
          rw [hb]
          right; use a
    . rintro (h1 | h2)
      . omega
      . omega


  let T := {(a, b, c) : ℕ × ℕ × ℕ | a ≤ 2008 ∧ b ≤ 2008 ∧ c ≤ 2008 ∧ (0 < b ∨ c = 2008)}

  have h_T_eq_T1: T = T1 := by
    unfold T1 T
    ext ⟨a, b, c⟩
    simp
    omega

  have h_T1_card: T1.card = 2008 * 2009^2 + 2009 := by
    rw [h_T1_eq_T2_T3]
    rw [Finset.card_union_of_disjoint]
    . unfold T2 T3
      simp
    . unfold T2 T3
      rw [Finset.disjoint_iff_ne]
      intro ⟨x1, y1, z1⟩ h1 ⟨x2, y2, z2⟩ h2
      simp at h1 h2
      obtain ⟨a, h21, h22, h23, h24⟩ := h2
      subst a
      obtain ⟨_, hy1, _⟩ := h1
      by_contra h
      simp at h
      obtain ⟨_, h_y_eq, _⟩ := h
      rw [h_y_eq] at hy1
      have : 1 ≤ y2 := hy1.1
      rw [← h23] at this
      omega

  have h_T_card: T.encard = 2008 * 2009^2 + 2009 := by
    rw [h_T_eq_T1, Set.encard_coe_eq_coe_finsetCard, h_T1_card]
    norm_cast

  let f1 : (ℕ × ℕ × ℕ) → ℕ := fun (a, b, c) => 2^a * 3^b * 5^c

  have hf1 : Set.InjOn f1 T := by
    unfold f1 T
    intro ⟨a, b, c⟩ hx ⟨a1, b1, c1⟩ hy hxy
    simp at hxy
    apply factorization_unique_2_3_5 at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    subst a b c
    rfl

  have h1 : f1 '' T = S := by
    unfold f1 T S
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists]
    constructor
    . rintro ⟨a, b, c, ⟨h1, h2, h3, h4⟩, rfl⟩
      have h_ne_0 : 2 ^ a * 3 ^ b * 5 ^ c ≠ 0 := by
        by_contra h
        simp at h
      have h_fac_2 : (2 ^ a * 3 ^ b * 5 ^ c).factorization 2 = a := by
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        simp
        rw [show (Nat.factorization 2) 2 = 1 by native_decide]
        rw [show (Nat.factorization 3) 2 = 0 by native_decide]
        rw [show (Nat.factorization 5) 2 = 0 by native_decide]
        simp
        all_goals by_contra h; simp at h

      have h_fac_3 : (2 ^ a * 3 ^ b * 5 ^ c).factorization 3 = b := by
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        simp
        rw [show (Nat.factorization 2) 3 = 0 by native_decide]
        rw [show (Nat.factorization 3) 3 = 1 by native_decide]
        rw [show (Nat.factorization 5) 3 = 0 by native_decide]
        simp
        all_goals by_contra h; simp at h

      have h_fac_5 : (2 ^ a * 3 ^ b * 5 ^ c).factorization 5 = c := by
        repeat rw [Nat.factorization_mul]
        repeat rw [Nat.factorization_pow]
        simp
        rw [show (Nat.factorization 2) 5 = 0 by native_decide]
        rw [show (Nat.factorization 3) 5 = 0 by native_decide]
        rw [show (Nat.factorization 5) 5 = 1 by native_decide]
        simp
        all_goals by_contra h; simp at h

      refine ⟨?_, ?_⟩
      . rw [← Nat.factorization_le_iff_dvd h_ne_0 (by omega)]
        intro n
        by_cases hn : n ∈ ({2, 3, 5} : Finset ℕ)
        . simp at hn
          rcases hn with (rfl | rfl | rfl)
          . rw [h_fac_2]
            rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 30) 2 = 1 by native_decide]
            omega
          . rw [h_fac_3]
            rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 30) 3 = 1 by native_decide]
            omega
          . rw [h_fac_5]
            rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 30) 5 = 1 by native_decide]
            omega
        . suffices (2 ^ a * 3 ^ b * 5 ^ c).factorization n = 0 by rw [this]; omega
          repeat rw [Nat.factorization_mul]
          repeat rw [Nat.factorization_pow]
          simp
          . refine ⟨⟨?_, ?_⟩, ?_⟩
            . right
              rw [Nat.factorization_eq_zero_iff]
              by_contra h
              simp at h
              obtain ⟨h1, h2⟩ := h
              apply Nat.le_of_dvd (by omega) at h2
              interval_cases n
              . contrapose h1; decide
              . contrapose h1; decide
              . simp at hn
            . right
              rw [Nat.factorization_eq_zero_iff]
              by_contra h
              simp at h
              obtain ⟨h1, h2⟩ := h
              apply Nat.le_of_dvd (by omega) at h2
              interval_cases n
              all_goals contrapose h1; try decide
              all_goals simp at hn

            . right
              rw [Nat.factorization_eq_zero_iff]
              by_contra h
              simp at h
              obtain ⟨h1, h2⟩ := h
              apply Nat.le_of_dvd (by omega) at h2
              interval_cases n
              all_goals contrapose h1; try decide
              all_goals simp at hn

          all_goals by_contra h; simp at h
      . by_contra h
        rw [← Nat.factorization_le_iff_dvd h_ne_0 (by omega)] at h
        rcases h4 with (h4 | h4)
        . have := h 3
          rw [h_fac_3] at this
          rw [Nat.factorization_pow] at this
          simp at this
          rw [show (Nat.factorization 20) 3 = 0 by native_decide] at this
          omega
        . have := h 5
          rw [h_fac_5] at this
          rw [Nat.factorization_pow] at this
          simp at this
          rw [show (Nat.factorization 20) 5 = 1 by native_decide] at this
          omega

    . intro ⟨hx1, hx2⟩
      have h_x_ne_0 : x ≠ 0 := by
        intro h
        simp only [h, zero_dvd_iff] at hx1
        omega

      use x.factorization 2
      use x.factorization 3
      use x.factorization 5
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      . rw [← Nat.factorization_le_iff_dvd] at hx1
        have := hx1 2
        rw [Nat.factorization_pow] at this
        simp at this
        rw [show (Nat.factorization 30) 2 = 1 by native_decide] at this
        all_goals omega
      . rw [← Nat.factorization_le_iff_dvd] at hx1
        have := hx1 3
        rw [Nat.factorization_pow] at this
        simp at this
        rw [show (Nat.factorization 30) 3 = 1 by native_decide] at this
        all_goals omega
      . rw [← Nat.factorization_le_iff_dvd] at hx1
        have := hx1 5
        rw [Nat.factorization_pow] at this
        simp at this
        rw [show (Nat.factorization 30) 5 = 1 by native_decide] at this
        all_goals omega
      . have h_x_fac : x.primeFactors ⊆ {2, 3, 5} := by
          rw [show ({2, 3, 5} : Finset ℕ) = Nat.primeFactors (30^2008) by native_decide]
          exact Nat.primeFactors_mono hx1 (by omega)

        rw [← Nat.factorization_le_iff_dvd h_x_ne_0 (by omega)] at hx1
        have h_x_fac_2 : x.factorization 2 ≤ 2008 := by
          have := hx1 2
          rw [Nat.factorization_pow] at this
          simp at this
          rw [show (Nat.factorization 30) 2 = 1 by native_decide] at this
          omega
        have h_x_fac_3 : x.factorization 3 ≤ 2008 := by
          have := hx1 3
          rw [Nat.factorization_pow] at this
          simp at this
          rw [show (Nat.factorization 30) 3 = 1 by native_decide] at this
          omega
        have h_x_fac_5 : x.factorization 5 ≤ 2008 := by
          have := hx1 5
          rw [Nat.factorization_pow] at this
          simp at this
          rw [show (Nat.factorization 30) 5 = 1 by native_decide] at this
          omega


        contrapose hx2
        simp at hx2
        obtain ⟨hx2, hx3⟩ := hx2
        simp only [Decidable.not_not]
        rw [← Nat.factorization_le_iff_dvd h_x_ne_0 (by omega)]
        intro n
        by_cases hn : n ∈ ({2, 3, 5} : Finset ℕ)
        . simp at hn
          rcases hn with (rfl | rfl | rfl)
          . rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 20) 2 = 2 by native_decide]
            omega
          . rw [hx2]
            omega
          . rw [Nat.factorization_pow]
            simp
            rw [show (Nat.factorization 20) 5 = 1 by native_decide]
            omega
        . suffices x.factorization n = 0 by rw [this]; omega
          rw [Nat.factorization_eq_zero_iff]
          by_contra h
          simp at h
          obtain ⟨h1, h2, h3⟩ := h
          have : n ∈ x.primeFactors := by
            simp
            refine ⟨?_, ?_, ?_⟩
            . exact h1
            . exact h2
            . exact h3
          have := h_x_fac this
          contrapose this
          exact hn

      . have h1 := prime_factor_of_dvd_n_pow_eq_n_prime_factor (show 0 < 30 by norm_num) hx1
        rw [show Nat.primeFactors 30 = {2, 3, 5} by native_decide] at h1
        have h2 := @factorization_subset_primeFactors x {2, 3, 5} (by omega) h1 (by intro p hp; simp at hp; rcases hp with (rfl | rfl | rfl); all_goals decide)
        rw [Finset.prod_insert (by simp)] at h2
        rw [Finset.prod_pair (by norm_num)] at h2
        nth_rw 4 [← h2]
        ring

  have h3 := Set.InjOn.encard_image hf1
  rw [h1, h_T_card] at h3
  exact h3
