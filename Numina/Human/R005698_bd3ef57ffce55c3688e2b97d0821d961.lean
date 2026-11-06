import Mathlib

-- we first prove a lemma to take out a odd prime factor from an integer which is not power of 2
lemma lemma_0 (n: ℕ) (h: 1 ≤ n) (f: ∀ x, n ≠ 2 ^ x): ∃ p, Nat.Prime p ∧ Odd p ∧ p ∣ n := by

  by_contra! s

  -- we first show that 2 ∣ n
  have d: 2 ∣ n := by
    by_contra! r
    -- then we can take any primefactor of n
    have v: ¬ Nat.Coprime n n := by
      rw [Nat.coprime_self]
      by_contra! j
      specialize f 0
      simp [j] at f
    rw [Nat.Prime.not_coprime_iff_dvd] at v
    obtain ⟨p, hp, h1, h2⟩ := v
    have up: Odd p := by
      apply Nat.Prime.odd_of_ne_two
      tauto
      by_contra! o
      rw [o] at h1
      tauto
    specialize s p hp up
    tauto

  -- then we show that n is power of a prime to derive contradiction
  have g: IsPrimePow n := by
    rw [isPrimePow_iff_card_primeFactors_eq_one]
    suffices n.primeFactors = {2} by simp [this]
    ext p
    constructor
    .
      intro l
      simp at l
      simp
      specialize s p
      simp [l] at s
      rw [Nat.Prime.even_iff] at s
      tauto
      tauto
    .
      intro l
      simp at l
      simp [l]
      refine ⟨(by norm_num), (by tauto), (by omega)⟩
  rw [isPrimePow_nat_iff ] at g
  obtain ⟨p, k, hp, h1, h2⟩ := g
  have y: p = 2 := by
    by_contra! y
    replace y: Odd p := by
      apply Nat.Prime.odd_of_ne_two
      tauto
      tauto
    specialize s p hp y
    absurd s
    rw [← h2]
    rw [show k = k - 1 + 1 by omega]
    ring_nf
    simp
  rw [y] at h2
  specialize f k
  tauto

-- then we prove the key lemma to derive the condition for the expression
lemma lemma_1 (n: ℕ) (h: 1 ≤ n): (∃ x y : ℕ, x > 0 ∧ y > 0 ∧ n = ⌈x / (2: ℚ)⌉ + y + x * y) ↔
  ¬ (∃ s, n = 2 ^ s ∧ Nat.Prime (2 * n + 1)) := by

  constructor

  -- the forward direction
  .
    intro f
    obtain ⟨x, y, h1, h2, h3⟩ := f
    by_contra! g
    obtain ⟨s, h4, h5⟩ := g
    by_cases r: Even x

    -- case when x = 2k
    .
      rw [even_iff_exists_two_mul] at r
      obtain ⟨k, r⟩ := r
      have o: ⌈x / (2: ℚ)⌉ = k := by
        simp [r]
      rw [o] at h3
      clear o
      norm_cast at h3
      replace h3: 2 * n + 1 = (2 * k + 1) * (2 * y + 1) := by
        nlinarith
      have u: (2 * n + 1) ∣ (2 * k + 1) * (2 * y + 1) := by
        rw [h3]
      rw [Nat.Prime.dvd_mul] at u
      rcases u with u | u
      .
        apply Nat.le_of_dvd at u
        rw [h3] at u
        absurd u
        simp
        by_contra! i
        simp [i] at h2
        omega
      .
        apply Nat.le_of_dvd at u
        rw [h3] at u
        absurd u
        simp
        by_contra! i
        omega
        omega
      tauto
    .
      -- case when x = 2k + 1
      simp at r
      apply Odd.exists_bit1 at r
      obtain ⟨t, r⟩ := r
      set k:= t + 1
      replace r: x = 2 * k - 1 := by
        omega
      clear_value k
      -- we first take out the ceil
      have o: ⌈x / (2: ℚ)⌉ = k := by
        rw [r]
        rw [Int.ceil_eq_iff]
        simp
        constructor
        .
          rw [lt_div_iff₀ ]
          have o: ↑(2 * k - 1) = 2 * k - (1: ℚ) := by
            have i: 1 ≤ 2 * k := by
              omega
            apply Nat.cast_sub at i
            rw [i]
            simp
          rw [o]
          have j: 0 ≤ k := by
            omega
          qify at j
          linarith
          norm_num
        .
          rw [div_le_iff₀']
          have o: ↑(2 * k - 1) = 2 * k - (1: ℚ) := by
            have i: 1 ≤ 2 * k := by
              omega
            apply Nat.cast_sub at i
            rw [i]
            simp
          rw [o]
          linarith
          norm_num
      rw [o] at h3
      clear o
      norm_cast at h3
      simp [r] at h3
      replace h3: n = (2 * y + 1) * k := by
        qify at h3
        have o: ↑(2 * k - 1) = 2 * k - (1: ℚ) := by
            have i: 1 ≤ 2 * k := by
              omega
            apply Nat.cast_sub at i
            rw [i]
            simp
        rw [o] at h3
        qify
        clear *- h3
        rw [h3]
        ring
      rw [h4] at h3
      have h6: 2 * y + 1 ∣ 2 ^ s := by
        rw [h3]
        simp
      have j: Nat.Coprime (2 * y + 1) (2 ^ s) := by
        apply Nat.Prime.coprime_pow_of_not_dvd
        norm_num
        by_contra! g
        replace g: 2 ∣ 1 := by
          rw [show 1 = 2 * y + 1 - 2 * y by omega]
          apply Nat.dvd_sub
          tauto
          tauto
          simp
        norm_num at g
      rw [h3] at j
      rw [Nat.coprime_mul_iff_right] at j
      rcases j with ⟨p, q⟩
      rw [Nat.coprime_self] at p
      omega

  -- the backward direction
  .
    intro f
    by_cases j: ¬ Nat.Prime (2 * n + 1)

    -- case when 2n + 1 is not prime
    .
      -- we first take one prime factor of 2n + 1
      have v: ¬ Nat.Coprime (2 * n + 1) (2 * n + 1) := by
        rw [Nat.coprime_self]
        omega
      rw [Nat.Prime.not_coprime_iff_dvd] at v
      obtain ⟨p, hp⟩ := v
      rcases hp with ⟨hp, h1, h2⟩
      clear h2
      have up: Odd p := by
        apply Nat.Prime.odd_of_ne_two
        tauto
        by_contra! o
        rw [o] at h1
        replace h1: 2 ∣ 1 := by
          rw [show 1 = 2 * n + 1 - 2 * n by omega]
          apply Nat.dvd_sub
          tauto
          tauto
          simp
        norm_num at h1
      apply Odd.exists_bit1 at up
      obtain ⟨k, hk⟩ := up
      set q:= (2 * n + 1) / p
      have s: p * q = 2 * n + 1 := by
        simp [q]
        apply Nat.mul_div_cancel'
        tauto
      have r:= j
      have j: Odd q := by
        by_contra! j
        simp at j
        apply Even.two_dvd  at j
        replace j: 2 ∣ 2 * n + 1 := by
          rw [← s]
          have i: q ∣ p * q := by simp
          apply dvd_trans j i
        replace j: 2 ∣ 1 := by
          rw [show 1 = 2 * n + 1 - 2 * n by omega]
          apply Nat.dvd_sub
          tauto
          tauto
          simp
        norm_num at j
      apply Odd.exists_bit1 at j
      obtain ⟨y, j⟩ := j
      use 2 * k, y
      refine ⟨?_, ?_, ?_⟩
      .
        by_contra! o
        replace o: k = 0 := by omega
        simp [o] at hk
        simp [hk] at hp
        norm_num at hp
      .
        by_contra! o
        replace o: y = 0 := by omega
        simp [o] at j
        simp [j] at s
        rw [← s] at r
        tauto
      .
        have u: ⌈↑(2 * k) / (2: ℚ)⌉ = k := by
          simp
        rw [u]
        norm_cast
        simp [hk, j] at s
        nlinarith

    -- case when 2n+1 is prime
    .
      simp [j] at f
      simp at j
      -- we need to find an odd prime factor of n
      have g:= lemma_0 n h f
      obtain ⟨p, hp, up, d⟩ := g
      apply Odd.exists_bit1 at up
      obtain ⟨y, hy⟩ := up
      set k:= n / (2 * y + 1)
      have hx: n = k * (2 * y + 1) := by
        simp [k]
        symm
        apply Nat.div_mul_cancel
        rw [← hy]
        tauto
      use (2 * k - 1), y
      refine ⟨?_, ?_, ?_⟩
      .
        suffices k ≠ 0 by omega
        by_contra! r
        simp [r] at hx
        simp [hx] at h
      .
        by_contra! v
        replace v: y = 0 := by omega
        simp [v] at hy
        simp [hy] at hp
        norm_num at hp
      .
        have o: ⌈↑(2 * k - 1) / (2: ℚ)⌉ = k := by
          rw [Int.ceil_eq_iff]
          simp
          have i: 1 ≤ 2 * k := by
            suffices k ≠ 0 by omega
            by_contra! r
            simp [r] at hx
            simp [hx] at h
          constructor
          .
            rw [lt_div_iff₀ ]
            have o: ↑(2 * k - 1) = 2 * k - (1: ℚ) := by
              apply Nat.cast_sub at i
              rw [i]
              simp
            rw [o]
            qify at i
            linarith
            norm_num
          .
            rw [div_le_iff₀']
            have o: ↑(2 * k - 1) = 2 * k - (1: ℚ) := by
              apply Nat.cast_sub at i
              rw [i]
              simp
            rw [o]
            linarith
            norm_num
        rw [o]
        have o1: ↑(2 * k - 1) = 2 * k - (1: ℤ) := by
          have i: 1 ≤ 2 * k := by
            suffices k ≠ 0 by omega
            by_contra! r
            simp [r] at hx
            simp [hx] at h
          apply Int.natCast_sub at i
          rw [i]
          simp
        rw [o1]
        zify at hx
        nlinarith

/-
 Find the sum of all positive integers $n \leq 2015$ that can be expressed in the form $\left\lceil\frac{x}{2}\right\rceil+y+x y$,
 where $x$ and $y$ are positive integers.
Answer: 2029906 Lemma: $n$ is expressible as $\left\lceil\frac{x}{2}\right\rceil+y+x y$ iff $2 n+1$ is not a Fermat Prime.. -/

theorem number_theory_609472:
    ∑ᶠ n ∈ {n : ℕ | 1 ≤ n ∧ n ≤ 2015 ∧ ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ n = ⌈x / (2: ℚ)⌉ + y + x * y}, n = 2030981 := by

    set s1:= {n : ℕ | 1 ≤ n ∧ n ≤ 2015 ∧ ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ n = ⌈x / (2: ℚ)⌉ + y + x * y}
    set s2:= ({1, 2, 8, 128}: Set ℕ)
    set s3:= ((Finset.Icc 1 2015): Set ℕ)

    -- we show that s3 is just the disjoint union of s1 and s2
    have i: ∑ᶠ n ∈ s3, n = ∑ᶠ n ∈ s1, n + ∑ᶠ n ∈ s2, n := by

      have u: s3 = s1 ∪ s2 := by
        ext n
        constructor

        -- the forward direction
        .
          intro h
          simp [s3] at h
          simp only [s1, s2]
          rw [Set.mem_union]
          by_cases i: n ∈ ({1, 2, 8, 128}: Set ℕ)
          .
            right
            tauto
          .
            left
            rw [Set.mem_setOf]
            refine ⟨(by omega), (by omega), ?_⟩
            rw [lemma_1]
            by_contra! f
            absurd i
            simp
            obtain ⟨s, h1, h2⟩ := f
            have ls: s ≤ 11 := by
              clear *- h h1
              by_contra! o
              replace o: 2 ^ 11 < 2 ^ s := by
                apply Nat.pow_lt_pow_of_lt
                norm_num
                tauto
              rw [← h1] at o
              linarith
            rw [h1]
            by_contra! f
            absurd h2
            rw [h1]
            clear *- f ls
            interval_cases s
            all_goals try norm_num
            all_goals try norm_num at f
            omega


        -- the backward direction
        .
          intro h
          simp [s1, s2] at h
          simp [s3]
          omega

      have v: Disjoint s1 s2 := by
        intro t h j
        simp at h j
        simp
        ext n
        simp
        by_contra! i
        replace h: n ∈ s1 := by
          apply Set.mem_of_mem_of_subset i h
        replace j: n ∈ s2 := by
          apply Set.mem_of_mem_of_subset i j
        simp only [s1, s2] at h j
        rw [Set.mem_setOf] at h
        rcases h with ⟨l1, l2, h⟩
        have f:= lemma_1 n (by omega)
        rw [f] at h
        clear f
        absurd h
        clear h
        simp at j
        clear *- j
        rcases j with j | j | j | j
        all_goals rw [j]
        .
          use 0
          norm_num
        .
          use 1
          norm_num
        .
          use 3
          norm_num
        .
          use 7
          norm_num

      have w: s3.Finite := by
        simp only [s3]
        apply Finset.finite_toSet

      rw [u]
      rw [finsum_mem_union]
      .
        exact v
      .
        suffices s1 ⊆ s3 by
         apply Set.Finite.subset at this
         tauto
         tauto
        intro x h
        simp [s1] at h
        simp [s3]
        omega
      .
        suffices s2 ⊆ s3 by
         apply Set.Finite.subset at this
         tauto
         tauto
        intro x h
        simp [s2] at h
        simp [s3]
        omega

    -- then it suffices to calculate s1 and s2
    suffices ∑ᶠ n ∈ s3, n = 2031120 ∧
      ∑ᶠ n ∈ s2, n = 139 by simp [this] at i; tauto
    refine ⟨?_, ?_⟩
    .
      simp only [s3]
      rw [finsum_mem_coe_finset]
      native_decide
    .
      simp only [s2]
      rw [finsum_mem_eq_toFinset_sum]
      simp
