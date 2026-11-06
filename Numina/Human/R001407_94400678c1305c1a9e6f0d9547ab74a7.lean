import Mathlib

open Finset

/- Any non-zero natural number n can be expressed as production of primes -/
lemma pow_factorization_eq_self_of_subset {n : ℕ} {N : Finset ℕ} (hn : n ≠ 0) (hn' : n.primeFactors ⊆ N) : n = ∏ p ∈ N, p ^ (n.factorization p) := by
  nth_rw 1 [←Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  apply prod_subset hn'
  intro x hx hx'
  have : n.factorization x = 0 := by
    exact Finsupp.not_mem_support_iff.mp hx'
  simp [this]

/- Any set of integers positive integers, whose prime divisors are less than 26, contains two number whose product is a perfect square -/
lemma square_of_card_gt_512 {α : Type*} {M : Finset α} {f : α → ℕ} (hdvd : ∀ x ∈ M, ∀ p, p.Prime → p ∣ f x → p ≤ 26) (hM : M.card > 512) :
    ∃ a ∈ M, ∃ b ∈ M, a ≠ b ∧ IsSquare (f a * f b) := by
  -- there are 9 primes less than 26, which are 2, 3, 5, 7, 11, 13, 17, 19, and 23.
  -- The prime factorization of f i can be expressed as a vector of 9 elements, where each element is either 0 or 1, indicating whether the corresponding exponent is even or odd.
  let p := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  have hp_inj : Function.Injective p := by
    refine List.nodup_ofFn.mp ?_
    simp [p]
  have himage : {2, 3, 5, 7, 11, 13, 17, 19, 23} ⊆ univ.image p := by
    simp [p]
    exact fun ⦃a⦄ a ↦ a
  have hfactor {x : α} (hx : x ∈ M) : (f x).primeFactors ⊆ univ.image p := by
    apply subset_trans ?_ himage
    intro p hp
    simp at hp
    obtain h := hdvd x hx p hp.1 hp.2.1
    interval_cases p
    all_goals simp
    all_goals norm_num at hp
  have hfne {x : α} (hx : x ∈ M) : f x ≠ 0 := by
    intro h
    obtain hdvd := hdvd x hx 29 (by norm_num)
    simp [h] at hdvd
  -- There are 2 ^ 9 = 512 possible combinations of even and odd exponents for the prime factorization.
  -- Applying the pigeonhole principle, we can find two distinct integers f a, f b whose prime factorization has the same parity for each prime.
  let s : Finset α := M
  let t : Finset (Fin 9 → Fin 2) := univ
  have hcard : s.card > t.card * 1 := by
    simp [s, t]
    exact hM
  let g : α → (Fin 9 → Fin 2) := fun x => fun i => ⟨Nat.factorization (f x) (p i) % 2, Nat.mod_lt _ (by simp)⟩
  have hg : ∀ α ∈ s, g α ∈ t := by simp [t]
  obtain ⟨y, hy, hcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hcard
  obtain ⟨a, ha, b, hb, hne⟩ := one_lt_card.mp hcard
  simp [s] at ha hb
  use a, ha.1, b, hb.1, hne
  use ∏ i, (p i) ^ (((f a).factorization (p i) + (f b).factorization (p i)) / 2)
  -- Now, we prove that the product of f a and f b is a perfect square.
  have hprod {x : α} (hx : x ∈ M) : f x = ∏ i, (p i) ^ ((f x).factorization (p i)) := by
    nth_rw 1 [pow_factorization_eq_self_of_subset (hfne hx) (hfactor hx)]
    rw [prod_image]
    intro _ _ _ _ h
    apply hp_inj h
  have heq {i : Fin 9} : Even ((f a).factorization (p i) + (f b).factorization (p i)) := by
    refine Nat.even_iff.mpr ?_
    rw [Nat.add_mod]
    have : (f a).factorization (p i) % 2 = (f b).factorization (p i) % 2 := by
      suffices h : g a i = g b i
      · simp [g] at h
        exact h
      · rw [ha.2, hb.2]
    rw [this]
    apply Nat.even_iff.mp
    simp
  have hmul {i : Fin 9} : (f a).factorization (p i) + (f b).factorization (p i) = ((f a).factorization (p i) + (f b).factorization (p i)) / 2 * 2 := by
    exact Eq.symm (Nat.div_two_mul_two_of_even heq)
  nth_rw 1 [hprod ha.1, hprod hb.1]
  simp
  rw [←sq, ←prod_pow, ←prod_mul_distrib]
  congr
  ext i
  rw [←pow_mul, ←pow_add]
  congr 1
  exact hmul

/- Recursively apply the pigeonhole principal, we can obtain (#M - 512) / 2 pairs of distinct integers whose products are perfect squares -/
lemma exists_distinct_pairs_of_card_gt {M : Finset ℕ} (hdvd : ∀ x ∈ M, ∀ p, p.Prime → p ∣ x → p ≤ 26) (hM : M.card ≥ 512) :
    ∃ f g : Fin ((M.card - 512) / 2) → ℕ, Function.Injective f ∧ Function.Injective g ∧ Set.range f ⊆ M ∧ Set.range g ⊆ M ∧ Disjoint (Set.range f) (Set.range g) ∧ ∀ i, IsSquare (f i * g i) := by
  set n := (M.card - 512) / 2 with hn
  clear_value n
  -- The proof is by induction on n := (#M - 512) / 2.
  induction n generalizing M with
  | zero =>
    use 0, 0
    simp
    exact Function.injective_of_subsingleton ![]
  | succ n ih =>
    have hM_ge : n + 1 > 0 := by simp
    rw [hn] at hM_ge
    simp at hM_ge
    have hM : M.card > 512 := by
      apply Nat.add_le_of_le_sub hM at hM_ge
      apply lt_of_lt_of_le ?_ hM_ge
      norm_num
    obtain ⟨a, ha, b, hb, hab, hsq⟩ := square_of_card_gt_512 hdvd hM
    have hcard_ab : ({a, b} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_not_mem]
      · simp
      · simp [hab]
    let M' := M \ {a, b}
    have hdvd' : ∀ x ∈ M', ∀ p, p.Prime → p ∣ x → p ≤ 26 := by
      intro x hx p hp hpn
      simp [M'] at hx
      apply hdvd x hx.1 p hp hpn
    have hcard : M'.card = M.card - 2 := by
      rw [Finset.card_sdiff, hcard_ab]
      intro x hx
      simp at hx
      rcases hx with hx | hx <;> simp [hx]
      · exact ha
      · exact hb
    have hM' : M'.card ≥ 512 := by
      simp [hcard]
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      apply Nat.add_le_of_le_sub (le_of_lt hM) hM_ge
    have hsub : M' ⊆ M := by
      exact sdiff_subset
    have hn' : n = (#M' - 512) / 2 := by
      trans n + 1 - 1
      · simp
      · rw [hn]
        rw [←Nat.sub_mul_div]
        simp [M']
        rw [card_sdiff, hcard_ab]
        · rw [Nat.sub_sub, Nat.sub_sub]
        · intro x hx
          simp at hx
          rcases hx with hx | hx <;> simp [hx]
          · exact ha
          · exact hb
        · simp [hM_ge]
    obtain ⟨f, g, hf, hg, hrf, hrg, hfg, hsq'⟩ := ih hdvd' hM' hn'
    let f' : Fin (n + 1) → ℕ := Fin.cons a f
    let g' : Fin (n + 1) → ℕ := Fin.cons b g
    have hf' : Function.Injective f' := by
      refine Fin.cons_injective_iff.mpr ?_
      constructor
      · apply Set.not_mem_subset hrf
        simp [M']
      · exact hf
    have hg' : Function.Injective g' := by
      refine Fin.cons_injective_iff.mpr ?_
      constructor
      · apply Set.not_mem_subset hrg
        simp [M']
      · exact hg
    have hrf' : Set.range f' ⊆ M := by
      intro x hx
      simp [f'] at hx
      rcases hx with hx | hx
      · simp [hx, ha]
      · apply Set.mem_of_mem_of_subset ?_ hsub
        apply Set.mem_of_mem_of_subset ?_ hrf
        exact hx
    have hrg' : Set.range g' ⊆ M := by
      intro x hx
      simp [g'] at hx
      rcases hx with hx | hx
      · simp [hx, hb]
      · apply Set.mem_of_mem_of_subset ?_ hsub
        apply Set.mem_of_mem_of_subset ?_ hrg
        exact hx
    use f', g', hf', hg', hrf', hrg'
    constructor
    · simp [f', g']
      apply Set.disjoint_left.mpr
      intro x hx
      simp at hx
      rcases hx with hx | hx
      · simp [hx, hab]
        intro i
        have : g i ∈ M' := by
          apply Set.mem_of_mem_of_subset ?_ hrg
          exact Set.mem_range_self i
        simp [M'] at this
        exact this.2.1
      · have : x ∉ Set.range g := by
          apply Set.disjoint_left.mp hfg
          exact hx
        by_contra h
        apply Set.eq_of_not_mem_of_mem_insert h at this
        have hx : x ∈ M' := by
          apply Set.mem_of_mem_of_subset ?_ hrf
          exact hx
        simp [M', this] at hx
    · simp [f', g']
      intro i
      rcases Fin.eq_zero_or_eq_succ i with hi | hi
      · simp [hi]
        exact hsq
      · obtain ⟨j, hj⟩ := hi
        simp [hj]
        apply hsq'

/-1. (MON 1) ${ }^{\mathrm{IMO} 4}$ Given a set $M$ of 1985 positive integers, none of which has a prime divisor larger than 26 ,
 prove that the set has four distinct elements whose geometric mean is an integer.-/
theorem other_23948
    (M : Finset ℕ)
    (hpos : ∀ x ∈ M, x > 0)
    (hcard : M.card = 1985)
    (hdvd : ∀ n ∈ M, ∀ p, p.Prime → p ∣ n → p ≤ 26)
    : ∃ a b c d : ℕ, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ ∃ t : ℤ, (a * b * c * d : ℝ) ^ ((1 : ℝ) / 4) = t := by

  -- Check the cardinality of M is at least 512, which is required for our lemma.
  have hM : M.card ≥ 512 := by simp [hcard]
  -- Now we can apply the lemma to obtain pairs of distinct integers whose products are perfect squares.
  obtain ⟨f, g, hf, hg, hrf, hrg, hfg, hsq⟩ := exists_distinct_pairs_of_card_gt hdvd hM
  -- The number of pairs is (#M - 512) / 2, which is at least 736.
  let M' : Finset (Fin ((#M - 512) / 2)) := univ
  have hM' : M'.card > 512 := by
    simp [M']
    rw [hcard]
    norm_num
  -- Let F be the function that maps each index to the geometric mean of the two integers in the pair.
  -- Then, we obtain > 512 numbers.
  let F : Fin ((#M - 512) / 2) → ℕ := fun i => Nat.sqrt (f i * g i)
  have hF : ∀ i, F i ^ 2 = f i * g i := by
    intro i
    simp [F]
    refine (Nat.exists_mul_self' (f i * g i)).mp ?_
    obtain ⟨k, hk⟩ := hsq i
    use k
    rw [hk]
    ring
  have hdvd' : ∀ i ∈ M', ∀ p, p.Prime → p ∣ F i → p ≤ 26 := by
    intro i hi p hp hpn
    have hpn : p ∣ F i ^ 2 := by
      refine Dvd.dvd.pow hpn ?_
      simp
    rw [hF i] at hpn
    apply Nat.Prime.dvd_mul hp |>.mp at hpn
    rcases hpn with hpn | hpn
    · apply hdvd (f i) ?_ p hp hpn
      apply Set.mem_of_mem_of_subset ?_ hrf
      exact Set.mem_range_self i
    · apply hdvd (g i) ?_ p hp hpn
      apply Set.mem_of_mem_of_subset ?_ hrg
      exact Set.mem_range_self i
  -- Therefore, we can again apply the lemma to obtain a pair of numbers a b such that product of F a, F b is a perfect square.
  obtain ⟨a, ha, b, hb, hab, hsq'⟩ := square_of_card_gt_512 hdvd' hM'
  have h₁ : f a ∈ Set.range f := by
    exact Set.mem_range_self a
  have h₂ : g a ∈ Set.range g := by
    exact Set.mem_range_self a
  have h₃ : f b ∈ Set.range f := by
    exact Set.mem_range_self b
  have h₄ : g b ∈ Set.range g := by
    exact Set.mem_range_self b
  -- The four distinct integers we are looking for are f a, f b, g a, g b.
  use f a, f b, g a, g b
  apply disjoint_iff_inf_le.mp at hfg
  simp at hfg
  split_ands
  · exact fun a_1 ↦ hab (hf a_1)
  · by_contra h
    rw [h] at h₁
    have : g a ∈ Set.range f ∩ Set.range g := by
      exact Set.mem_inter h₁ h₂
    simp [hfg] at this
  · by_contra h
    rw [h] at h₁
    have : g b ∈ Set.range f ∩ Set.range g := by
      exact Set.mem_inter h₁ h₄
    simp [hfg] at this
  · by_contra h
    rw [h] at h₃
    have : g a ∈ Set.range f ∩ Set.range g := by
      exact Set.mem_inter h₃ h₂
    simp [hfg] at this
  · by_contra h
    rw [h] at h₃
    have : g b ∈ Set.range f ∩ Set.range g := by
      exact Set.mem_inter h₃ h₄
    simp [hfg] at this
  · exact fun a_1 ↦ hab (hg a_1)
  · -- Note that f a * g a, f b * g b ∧ √(f a * g a) * √(f b * g b) are perfect squares.
    -- which implies that the geometric mean of these four integers is an integer.
    obtain ⟨k₁, hk₁⟩ := hsq a
    obtain ⟨k₂, hk₂⟩ := hsq b
    obtain ⟨k₃, hk₃⟩ := hsq'
    use k₃
    trans (k₁ * k₁ * (k₂ * k₂) : ℝ) ^ (1 / 4 : ℝ)
    · congr 1
      norm_cast
      rw [←hk₁, ←hk₂]
      ring
    trans √(k₁ * k₂)
    · rw [←sq, ←sq, ←Real.rpow_natCast, ←Real.rpow_natCast, Real.mul_rpow, ←Real.rpow_mul, ←Real.rpow_mul]
      norm_num
      simp [Real.sqrt_eq_rpow]
      all_goals positivity
    · apply Real.sqrt_eq_iff_mul_self_eq ?_ ?_ |>.mpr
      · norm_cast
        have : (k₁ * k₂) ^ 2 = (k₃ * k₃) ^ 2 := by
          rw [←hk₃, mul_pow, mul_pow, hF, hF, hk₁, hk₂]
          ring
        apply Nat.pow_left_injective ?_ this
        simp
      · positivity
      · positivity
