import Mathlib

/- The set $A$ consists of 2016 positive integers. All prime divisors of these numbers are smaller than 30. Prove that there are four distinct numbers $a, b, c$ and $d$ in $A$ such that abcd is a perfect square. -/
theorem number_theory_239606 (A : Finset ℕ) (hA : A.card = 2016)
  (hA1 : ∀ n ∈ A, n > 0) (hA2 : ∀ n ∈ A, ∀ p ∈ Nat.primeFactors n, p < 30) :
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ∃ m, m^2 = a * b * c * d := by

    -- there are 10 primes less than 30, listed as follows
    let ps := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    -- To each number n in A we can assign a 10-element sequance (b_1, …, b_10)
    -- such that b_i = 1 iff ps[i] has odd exponent in the factorizatino of n
    let χ (n : ℕ) : Fin 10 → Fin 2 := fun i ↦
      if Odd (n.factorization (ps.get i)) then 1 else 0

    -- There are only 1024 different 10-element {0, 1}-sequences
    let t : Finset (Fin 10 → Fin 2) := .univ
    have h_t_card : t.card = 2 ^ 10 := by simp [t]
    have h_χ_mem_t : ∀ n, χ n ∈ t := by intro n; simp [t]

    -- any number whose prime factors are smaller than 30
    -- has prime factors only within ps
    have h_prime_factors_subset_ps : ∀ a : ℕ,
      (∀ p ∈ a.primeFactors, p < 30) → a.primeFactors ⊆ ps.toFinset := by
        intro a amem p pmem
        have hp : Nat.Prime p := by simp [Nat.mem_primeFactors] at pmem; simp [pmem]
        have : p ≤ 29 := Nat.le_of_lt_succ (amem p pmem)
        interval_cases p
        all_goals norm_num at hp
        all_goals unfold ps; apply List.mem_toFinset.mpr; simp

    -- the sequence assigned to a * b is just the sum of suquences assigned to a and to b
    have h_χ_mul_eq_add (a b : ℕ) (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) :
      χ (a * b) = χ a + χ b := by
        ext i
        by_cases ha : Odd (a.factorization (ps.get i))
        all_goals by_cases hb : Odd (b.factorization (ps.get i))
        all_goals simp only [List.get_eq_getElem] at ha hb
        all_goals simp [χ, Nat.factorization_mul, ha₀, hb₀, ha, hb];
        · have := Nat.not_odd_iff_even.mpr <| Odd.add_odd ha hb
          simp [this]
        all_goals simp at ha hb
        · have := Odd.add_even ha hb
          simp [this]
        · have := Even.add_odd ha hb
          simp [this]
        · have := Nat.not_odd_iff_even.mpr <| Even.add ha hb
          simp [this]

    -- Two numbers to which identical sequences are assigned, multiply to a perfect square.
    have lem_issquare_of_χ_eq: ∀ a ∈ A, ∀ b ∈ A, χ a = χ b → IsSquare (a * b) := by
      intro a amem b bmem h_χ_eq
      have h_χ_ab : χ (a * b) = 0 := by
        have lem_fin_2_add_self (a : Fin 2) : a + a = 0 := by
          match a with
          | 0 | 1 => simp
        ext i
        simp
        rw [h_χ_mul_eq_add, h_χ_eq]
        simp [lem_fin_2_add_self]
        exact Nat.not_eq_zero_of_lt (hA1 a amem)
        exact Nat.not_eq_zero_of_lt (hA1 b bmem)

      have : ∀ p : ℕ, Nat.Prime p → Even ((a * b).factorization p) := by
        intro p p_prime
        by_cases hp : p ∈ (a * b).primeFactors
        · have : p ∈ ps := by
            have := h_prime_factors_subset_ps (a * b) ?_
            exact this hp
            rw [Nat.primeFactors_mul]
            intro p pmem_cup
            simp only [Finset.mem_union] at pmem_cup
            rcases pmem_cup with h | h
            · exact hA2 a amem p h
            · exact hA2 b bmem p h
            exact Nat.not_eq_zero_of_lt (hA1 a amem)
            exact Nat.not_eq_zero_of_lt (hA1 b bmem)
          have ⟨i, hi⟩ := List.mem_iff_get.mp this
          have : χ (a * b) i = 0 := by rw [h_χ_ab]; simp
          unfold χ at this
          rw [hi] at this
          simp at this
          exact this

        have : ¬  p ∣ a * b := by
          intro h_dvd
          have := Nat.mem_primeFactorsList_iff_dvd ?_ ?_ |>.mpr h_dvd
          have := Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr this
          exact hp this
          · have := hA1 a amem
            have := hA1 b bmem
            positivity
          · assumption
        have : (a * b).factorization p = 0 := by
          apply Nat.factorization_eq_zero_iff (a * b) p |>.mpr
          right; left
          exact this
        rw [this]
        trivial

      let n := a * b
      use n.factorization.prod fun p e ↦ p ^ (e / 2)
      rw [← Finsupp.prod_mul]
      rw [← Nat.factorization_prod_pow_eq_self (n := a * b)]
      unfold n

      · apply Finsupp.prod_congr
        intro p pmem
        simp at pmem
        have ⟨k, hk⟩ := this p pmem.1
        have : (a * b).factorization p / 2 = k := by
          rw [hk, ← mul_two]
          simp
        rw [this, hk]
        ring

      have := hA1 a amem
      have := hA1 b bmem
      positivity

    -- By pigeonhole principle, there exist some two numbers a and b
    -- with identical sequences
    have ⟨c₁, hc₁_mem, hc₁_card⟩ : ∃ c ∈ t, 2 ≤ {a ∈ A | χ a = c}.card := by
      apply Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      · intros; apply h_χ_mem_t
      · rw [h_t_card]
        linarith

    have ⟨a, b, amem, bmem, ab_ne⟩ := Finset.one_lt_card_iff.mp hc₁_card
    simp at amem bmem

    -- so a * b is a square
    have h_issquare_ab : IsSquare (a * b) := by
      apply lem_issquare_of_χ_eq a amem.1 b bmem.1
      trans c₁
      exact amem.2
      exact bmem.2.symm

    -- removing a and b from A, the remaining set consists 2014 integers
    let A' := A \ {a, b}
    have : A'.card ≥ 2014 := by
      calc
        A'.card ≥ A.card - ({a, b} : Finset ℕ).card := by
          apply Finset.le_card_sdiff
        _ = 2016 - 2 := by congr; exact Finset.card_pair ab_ne

    -- certainly two other numbers c and d with identical sequences remain
    have ⟨c₂, hc₂_mem, hc₂_card⟩ : ∃ c ∈ t, 2 ≤ {a ∈ A' | χ a = c}.card := by
      apply Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      · intros; apply h_χ_mem_t
      · rw [h_t_card]
        linarith

    have ⟨c, d, cmem, dmem, cd_ne⟩ := Finset.one_lt_card_iff.mp hc₂_card
    simp [A'] at cmem dmem

    -- and c * d is also a square
    have h_issquare_cd : IsSquare (c * d) := by
      apply lem_issquare_of_χ_eq c cmem.1.1 d dmem.1.1
      trans c₂
      exact cmem.2
      exact dmem.2.symm

    -- these a, b, c and d satisfy the condition of the problem
    use a, amem.1
    use b, bmem.1
    use c, cmem.1.1
    use d, dmem.1.1

    constructor
    · exact ab_ne
    constructor
    · exact fun x ↦ cmem.1.2.1 x.symm
    constructor
    · exact fun x ↦ dmem.1.2.1 x.symm
    constructor
    · exact fun x ↦ cmem.1.2.2 x.symm
    constructor
    · exact fun x ↦ dmem.1.2.2 x.symm
    constructor
    · exact cd_ne
    · have ⟨m, hm⟩ := h_issquare_ab
      have ⟨n, hn⟩ := h_issquare_cd
      use m * n
      rw [hm, mul_assoc, hn]
      ring
