import Mathlib

set_option maxRecDepth 3000

/- Let $T$ be the set of all positive integer divisors of $2004^{100}$. What is the largest possible number of elements that a subset $S$ of $T$ can have if no element of $S$ is an integer multiple of any other element of $S$ ? -/


lemma not_in_prime_factors_factorization_eq_zero {x p : ℕ} : p ∉ x.primeFactors → x.factorization p = 0 := by
  intro h
  rw [Nat.factorization_eq_zero_iff]
  contrapose h
  simp at h
  simp
  exact h

lemma prime_factors_2004_pow {n : ℕ} (hn : n ≠ 0): (2004 ^ n).primeFactors = {2, 3, 167} := by
  have : (2004 ^ n).primeFactors = (2004).primeFactors := by
    apply Nat.primeFactors_pow
    exact hn
  rw [this]
  native_decide

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

theorem number_theory_605052 (T : Finset ℕ) (hT : T = (Nat.divisors (2004^100))) :
    IsGreatest {x | ∃ S : Finset ℕ, S ⊆ T ∧ S.card = x ∧ ∀ m ∈ S, ∀ n ∈ S, m ≠ n → ¬(m ∣ n)} 10201 := by

  let T1 := Finset.image (fun (a, b, c) => 2^a * 3^b * 167^c) (Finset.range 201 ×ˢ Finset.range 101 ×ˢ Finset.range 101)
  let S1 := Finset.image (fun (b, c) => 2^(200 - b - c) * 3^b * 167^c) (Finset.range 101 ×ˢ Finset.range 101)

  have h_factor_T : ∀ x ∈ T, x.primeFactors ⊆ {2, 3, 167} := by
    intro x hx p hp
    rw [hT, Nat.mem_divisors] at hx
    have := Nat.primeFactors_mono hx.1 hx.2 hp
    rw [prime_factors_2004_pow (by norm_num)] at this
    exact this

  have hT1 : T1 = T := by
    ext x

    constructor
    . rw [hT, Nat.mem_divisors]
      unfold T1
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
      rintro ⟨a, b, c, ⟨ha, hb, hc⟩, hx⟩
      refine ⟨?_, by decide⟩
      use 2^(200-a)*3^(100-b)*167^(100-c)
      rw [← hx]
      rw [show 2 ^ a * 3 ^ b * 167 ^ c * (2 ^ (200 - a) * 3 ^ (100 - b) * 167 ^ (100 - c)) = 2 ^ a * 2 ^ (200 - a) * (3 ^ b * 3 ^ (100 - b)) * (167 ^ c * 167 ^ (100 - c)) by ring]
      repeat rw [← pow_add]
      rw [show a + (200 - a) = 200 by omega]
      rw [show b + (100 - b) = 100 by omega]
      rw [show c + (100 - c) = 100 by omega]
      ring
    . intro h
      have hx_factor := h_factor_T x h
      rw [hT, Nat.mem_divisors] at h
      obtain ⟨h1, h2⟩ := h
      unfold T1
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
      have h_x_ne_zero : x ≠ 0 := by
        by_contra h
        subst x
        simp at h1
      rw [← Nat.factorization_prime_le_iff_dvd h_x_ne_zero h2] at h1
      use x.factorization 2, x.factorization 3, x.factorization 167
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      . have := h1 2 (by norm_num)
        rw [Nat.factorization_pow] at this
        simp at this
        rw [show (Nat.factorization 2004) 2 = 2 by native_decide] at this
        omega
      . have := h1 3 (by norm_num)
        rw [Nat.factorization_pow] at this
        simp at this
        rw [show (Nat.factorization 2004) 3 = 1 by native_decide] at this
        omega
      . have := h1 167 (by norm_num)
        rw [Nat.factorization_pow] at this
        simp at this
        rw [show (Nat.factorization 2004) 167 = 1 by native_decide] at this
        omega
      . suffices ∏ p ∈ {2, 3, 167}, p ^ x.factorization p = x by
          nth_rw 4 [← this]
          rw [Finset.prod_insert (by norm_num)]
          rw [Finset.prod_pair (by norm_num)]
          ring
        apply factorization_subset_primeFactors
        . omega
        . exact hx_factor
        . intro p hp
          simp at hp
          rcases hp with rfl | rfl | rfl
          all_goals norm_num

  have hS1_subset_T1 : S1 ⊆ T1 := by
    unfold S1 T1
    intro x hx
    simp at hx ⊢
    obtain ⟨b, c, ⟨hb, hc⟩, hx⟩ := hx
    use 200 - b - c, b, c
    exact ⟨⟨by omega, hb, hc⟩, hx⟩

  have hT3 : ∀ x ∈ T, x ≠ 0 := by
    intro x h hx
    rw [hx, ← hT1] at h
    unfold T1 at h
    simp at h

  have hT2 : ∀ x y : ℕ, x ∈ T → y ∈ T → (∀ p ∈ ({2, 3, 167}: Finset ℕ), x.factorization p = y.factorization p) → x = y := by
    intro x y hx hy h
    apply Nat.eq_of_factorization_eq (hT3 x hx) (hT3 y hy)
    intro p
    by_cases hp : p ∈ ({2, 3, 167}: Finset ℕ)
    . exact h p hp
    . have hp1 : p ∉ x.primeFactors := by
        contrapose hp
        push_neg at hp ⊢
        exact h_factor_T x hx hp
      have hp2 : p ∉ y.primeFactors := by
        contrapose hp
        push_neg at hp ⊢
        exact h_factor_T y hy hp
      rw [not_in_prime_factors_factorization_eq_zero hp1]
      rw [not_in_prime_factors_factorization_eq_zero hp2]

  constructor
  . simp only [Set.mem_setOf_eq]
    use S1
    refine ⟨?_, ?_, ?_⟩
    . rw [← hT1]
      exact hS1_subset_T1
    . native_decide
    . unfold S1
      intro m hm n hn hmn
      simp at hm hn
      obtain ⟨m1, m2, ⟨hm1, hm2⟩, hm⟩ := hm
      obtain ⟨n1, n2, ⟨hn1, hn2⟩, hn⟩ := hn
      rintro ⟨u, hu⟩
      have h_u_ne_zero : u ≠ 0 := by
        by_contra h
        subst u
        simp at hu
        subst n
        simp at hu
      rw [← hm, ← hn] at hu
      have h1 : 200 - m1 - m2 ≤ 200 - n1 - n2 := by
        apply congrArg (fun x => x.factorization 2) at hu
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hu
        repeat rw [Nat.factorization_pow] at hu
        simp at hu
        rw [show (Nat.factorization 2) 2 = 1 by norm_num] at hu
        rw [show (Nat.factorization 3) 2 = 0 by norm_num] at hu
        rw [show (Nat.factorization 167) 2 = 0 by norm_num] at hu
        all_goals try simp
        all_goals omega

      have h2 : m1 ≤ n1 := by
        apply congrArg (fun x => x.factorization 3) at hu
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hu
        repeat rw [Nat.factorization_pow] at hu
        simp at hu
        rw [show (Nat.factorization 2) 3 = 0 by norm_num] at hu
        rw [show (Nat.factorization 3) 3 = 1 by norm_num] at hu
        rw [show (Nat.factorization 167) 3 = 0 by norm_num] at hu
        all_goals try simp
        all_goals omega

      have h3 : m2 ≤ n2 := by
        apply congrArg (fun x => x.factorization 167) at hu
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at hu
        repeat rw [Nat.factorization_pow] at hu
        simp at hu
        rw [show (Nat.factorization 2) 167 = 0 by norm_num] at hu
        rw [show (Nat.factorization 3) 167 = 0 by norm_num] at hu
        rw [show (Nat.factorization 167) 167 = 1 by norm_num] at hu
        all_goals try simp
        all_goals omega

      have : m1 = n1 := by omega
      have : m2 = n2 := by omega
      subst m1 m2
      omega

  . simp only [Set.mem_setOf_eq, upperBounds]
    rintro x ⟨S, hS1, hS2, hS3⟩
    by_contra hx
    simp at hx

    let S2 := Finset.range 101 ×ˢ Finset.range 101
    have h_S2_card : S2.card = 10201 := by
      unfold S2
      simp

    let f : ℕ → ℕ × ℕ := fun x => (x.factorization 3, x.factorization 167)
    have hcard : S2.card < S.card := by
      rw [hS2, h_S2_card]
      exact hx
    have hf : ∀ a ∈ S, f a ∈ S2 := by
      intro a ha
      have := hS1 ha
      rw [← hT1] at this
      unfold T1 at this
      simp at this
      obtain ⟨a1, a2, a3, ⟨ha1, ha2, ha3⟩, ha4⟩ := this
      have ha5 : a.factorization 3 = a2 := by
        apply congrArg (fun x => x.factorization 3) at ha4
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at ha4
        repeat rw [Nat.factorization_pow] at ha4
        simp at ha4
        rw [show (Nat.factorization 2) 3 = 0 by norm_num] at ha4
        rw [show (Nat.factorization 3) 3 = 1 by norm_num] at ha4
        rw [show (Nat.factorization 167) 3 = 0 by norm_num] at ha4
        simp at ha4
        rw [ha4]
        all_goals simp
      have ha6 : a.factorization 167 = a3 := by
        apply congrArg (fun x => x.factorization 167) at ha4
        repeat rw [Nat.factorization_mul, Finsupp.add_apply] at ha4
        repeat rw [Nat.factorization_pow] at ha4
        simp at ha4
        rw [show (Nat.factorization 2) 167 = 0 by norm_num] at ha4
        rw [show (Nat.factorization 3) 167 = 0 by norm_num] at ha4
        rw [show (Nat.factorization 167) 167 = 1 by norm_num] at ha4
        simp at ha4
        rw [ha4]
        all_goals simp
      unfold S2 f
      simp
      rw [ha5, ha6]
      exact ⟨ha2, ha3⟩

    have := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hf
    obtain ⟨y, hy, z, hz, hyz, heq⟩ := this
    rcases lt_trichotomy (y.factorization 2) (z.factorization 2) with hlt | h | hgt
    . have := hS3 y hy z hz hyz
      contrapose this
      simp
      rw [← Nat.factorization_le_iff_dvd (hT3 y (hS1 hy)) (hT3 z (hS1 hz))]
      intro p
      by_cases hp : p ∈ y.primeFactors
      . have := h_factor_T y (hS1 hy) hp
        simp at this
        unfold f at heq
        simp at heq
        obtain ⟨heq1, heq2⟩ := heq
        rcases this with h | h | h
        all_goals rw [h]; omega
      . suffices y.factorization p = 0 by
          rw [this]; omega
        rw [not_in_prime_factors_factorization_eq_zero hp]

    . contrapose hyz
      simp
      apply hT2
      . exact hS1 hy
      . exact hS1 hz
      . intro p hp
        simp at hp
        unfold f at heq
        simp at heq
        obtain ⟨heq1, heq2⟩ := heq
        rcases hp with h | h | h
        all_goals rw [h]; assumption

    . have := hS3 z hz y hy (Ne.symm hyz)
      contrapose this
      simp
      rw [← Nat.factorization_le_iff_dvd (hT3 z (hS1 hz)) (hT3 y (hS1 hy))]
      intro p
      by_cases hp : p ∈ z.primeFactors
      . have := h_factor_T z (hS1 hz) hp
        simp at this
        unfold f at heq
        simp at heq
        obtain ⟨heq1, heq2⟩ := heq
        rcases this with h | h | h
        all_goals rw [h]; omega
      . suffices z.factorization p = 0 by
          rw [this]; omega
        rw [not_in_prime_factors_factorization_eq_zero hp]
