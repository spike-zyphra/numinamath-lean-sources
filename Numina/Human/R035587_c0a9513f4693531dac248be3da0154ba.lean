import Mathlib

/- De rij positieve gehele getallen $a_{0}, a_{1}, a_{2}, \ldots$ is gedefinieerd door $a_{0}=3$ en

$$
a_{n+1}-a_{n}=n\left(a_{n}-1\right)
$$

voor alle $n \geq 0$. Bepaal alle gehele getallen $m \geq 2$ waarvoor geldt dat $\operatorname{ggd}\left(m, a_{n}\right)=1$ voor alle $n \geq 0$. -/
theorem number_theory_605004
  (a : ℕ → ℤ) (ha₀ : a 0 = 3) (ha₁ : ∀ n : ℕ, a (n + 1) - a n = n * (a n - 1))
  {m : ℕ} (hm : 2 ≤ m) :
  (∀ n : ℕ, Int.gcd m (a n) = 1) ↔ ∃ i : ℕ, 1 ≤ i ∧ m = 2 ^ i := by
  -- Translation of problem:
  --  Given integer sequence a_0, a_1, a_2, ... defined by
  --  a_0 = 3 and a_{n+1} - a_n = n(a_n - 1) for all n ≥ 0
  --  find all integers m ≥ 2 such that gcd(m, a_n) = 1 for all n ≥ 0
  -- Answer: m = 2^i for some i ≥ 1

  -- First we need a couple of lemmas.

  -- the explicit expression for 'a n', proved by induction
  have a_explicit : ∀ n : ℕ, a n = 2 * n.factorial + 1 := by
    intro n
    induction n
    case zero => simp [ha₀]
    case succ n ih =>
      have : a (n + 1) = a n + n * (a n - 1) := by linarith [ha₁ n]
      rw [this, ih]
      simp [Nat.factorial_succ]
      norm_cast
      ring

  -- this is for the 'only if' part, showing that every m = power of 2 satisfy
  -- the condition that ∀ n, gcd(m, a n) = 1
  have two_pow_gcd_one (i : ℕ) : ∀ n : ℕ, Int.gcd ((2 ^ i) : ℕ) (a n) = 1 := by
    intro n
    rw [a_explicit] -- rewrite 'a n' by its explicit form, then clearly it is odd
    norm_cast
    induction i
    case zero => simp
    case succ i ih =>
      rw [pow_succ]
      apply Nat.coprime_iff_gcd_eq_one.mp
      apply Nat.Coprime.mul
      · apply Nat.coprime_iff_gcd_eq_one.mpr
        exact ih
      simp

  -- this lemma states that any number that is not a power of 2 has a
  -- prime factor ≥ 3
  let rec prime_fac_of_non_pow_2
    (n : ℕ) (nge2 : n ≥ 2) (h : ∀ (i : ℕ), 1 ≤ i → n ≠ 2 ^ i) :
    ∃ p, p ≥ 3 ∧ Nat.Prime p ∧ p ∣ n := by
    -- divide into even and odd cases
    rcases Nat.even_or_odd n with he | ho

    -- case 1 : n is even, we use recursion on n / 2
    · have ⟨t, ht⟩ := he
      rw [(by ring : t + t = 2 * t)] at ht

      -- t is n / 2, we show that t is not a power of 2, as n is not.
      have ht_non_pow : ∀ (i : ℕ), 1 ≤ i → t ≠ 2 ^ i := by
        by_contra! hi
        obtain ⟨i, hi⟩ := hi
        have : n = 2 ^ (i + 1) := by
          rw [pow_add, ht, hi.2]
          ring
        have i_succ_ge_1 : i + 1 ≥ 1 := by linarith
        have := h (i + 1) i_succ_ge_1
        contradiction

      -- the condition t ≥ 2 is needed for recursion
      have ht_ge_2 : t ≥ 2 := by
        by_contra! h''
        have : n = 2 := by linarith
        have ⟨i, hc⟩ : ∃ (i : ℕ), 1 ≤ i ∧ n = 2 ^ i := by
          use 1
          simp_all
        have := h i hc.1
        have := hc.2
        contradiction

      -- get a prime factor ≥ 3 of t by recursion
      have ⟨p, ⟨hp_ge_3, hp_prime, hp_dvd_t⟩⟩ := prime_fac_of_non_pow_2 t ht_ge_2 ht_non_pow

      -- this factor p is also a factor of n
      use p
      simp_all
      exact Dvd.dvd.mul_left hp_dvd_t 2

    -- case 2 : n is odd, its minimum prime factor must be at least 3
    · have : n.minFac ≥ 3 := by
        by_contra! h'
        have : n.minFac ≥ 2 := by
          have : Nat.Prime n.minFac := by
            apply Nat.minFac_prime
            linarith
          exact Nat.Prime.two_le this
        have : n.minFac = 2 := by linarith
        have : 2 ∣ n := by
          exact (Nat.minFac_eq_two_iff n).mp this
        have : Even n := by
          exact (even_iff_exists_two_nsmul n).mpr this
        have := Nat.not_odd_iff_even.mpr this
        contradiction

      -- so we just use the minimum prime factor of n
      use n.minFac
      simp [this]
      constructor
      · apply Nat.minFac_prime
        linarith
      · exact Nat.minFac_dvd n

  -- core lemma of the proof, which states that for any prime number p ≥ 3,
  -- p divides a (p - 3) = 2 * (p - 3)! + 1
  have p_dvd_a_p_sub_3 (p : ℕ) (hp : Nat.Prime p) (hp' : p ≥ 3) :
    (p : ℤ) ∣ 2 * (p - 3).factorial + 1 := by

    -- introduce this in order to call wilson_lemma
    have fact_p_prime : Fact (Nat.Prime p) := by exact { out := hp }

    -- we start by changing the goal step by step.

    -- 1. we turn the goal into the form of congruence
    suffices h : 2 * (p - 3).factorial + 1 ≡ 0 [ZMOD p] by
      exact Int.dvd_of_emod_eq_zero h

    -- 2. move the '1' to RHS
    suffices h : 2 * (p - 3).factorial ≡ -1 [ZMOD p] by
      have := Int.ModEq.add_right 1 h
      simp at this
      exact this

    -- 3. multiply -1 on both sides
    suffices h : 2 * (p - 3).factorial * (-1) ≡ 1 [ZMOD p] by
      have := Int.ModEq.mul_right (-1) h
      simp at this
      exact this

    -- 4. multiply -2 on both sides
    suffices h : 2 * (p - 3).factorial * (-2) * (-1) ≡ -2 [ZMOD p] by
      rw [mul_assoc] at h
      nth_rw 3 [mul_comm] at h
      rw [← mul_assoc] at h
      nth_rw 2 [(by rfl : -2 = 1 * (-2))] at h
      have pge0 : 0 < (p : ℤ) := by linarith
      have := Int.ModEq.cancel_right_div_gcd pge0 h
      have pmod2 : (p : ℤ).gcd (-2) = 1 := by
        unfold Int.gcd
        norm_cast
        simp
        have := Nat.Prime.eq_two_or_odd' hp
        rcases this with h | h <;> simp_all
      rw [pmod2] at this
      simp_all

    -- 5. divide 2 on both sides
    suffices h : (p - 3).factorial * (-2) * (-1) ≡ -1 [ZMOD p] by
      simp_all
      have := Int.ModEq.mul_left 2 h
      simp at this
      rw [← mul_assoc] at this
      exact this

    -- 6. change (-2) into (p - 2) and (-1) into (p - 1)
    have p_sub_2 : p - 2 ≡ -2 [ZMOD p] := by
      apply Int.modEq_iff_add_fac.mpr
      use -1
      ring
    have p_sub_1 : p - 1 ≡ -1 [ZMOD p] := by
      apply Int.modEq_iff_add_fac.mpr
      use -1
      ring
    suffices h : (p - 3).factorial * (p - 2) * (p - 1) ≡ -1 [ZMOD p] by
      calc
        (p - 3).factorial * (-2) * (-1)
          ≡ (p - 3).factorial * (-2) * (p - 1) [ZMOD p] := by
            apply Int.ModEq.mul; rfl; exact p_sub_1.symm
        _ ≡ (p - 3).factorial * (p - 1) * (-2) [ZMOD p] := by
            rw [mul_assoc]; nth_rw 2 [mul_comm]; rw [← mul_assoc]
        _ ≡ (p - 3).factorial * (p - 1) * (p - 2) [ZMOD p] := by
            apply Int.ModEq.mul; rfl; exact p_sub_2.symm
        _ ≡ -1 [ZMOD p] := by
            rw [mul_assoc]; nth_rw 2 [mul_comm]; rw [← mul_assoc]; exact h

    -- change LHS to (p - 1)!
    have : ((p - 3).factorial : ℤ) * ((p : ℤ) - 2) * (p - 1) = (p - 1).factorial := by
      have : p - 1 = p - 3 + 1 + 1 := by
        simp_all; rw [add_assoc];
        simp
        exact (Nat.sub_eq_iff_eq_add hp').mp rfl
      rw [this]
      simp [Nat.factorial_succ]
      have : (p : ℤ) - 2 = (↑(p - 3)) + 1 := by
        have : ↑ (p - 3) = (p : ℤ) - 3 := by norm_cast
        rw [this]
        ring
      rw [← this]
      have : (p : ℤ) - 1 = (↑p - 2) + 1 := by ring
      rw [← this]
      ring

    rw [this]
    refine (ZMod.intCast_eq_intCast_iff ?_a (-1 : ℤ) p).mp ?_h
    simp  -- simp knows Wilson's Theorem!

  -- Finally we prove the theorem
  constructor
  -- 1. necessity
  · intro h
    by_contra! hne
    obtain ⟨p, ⟨hp_ge_3, hp_prime, hp_dvd_m⟩⟩ := prime_fac_of_non_pow_2 m hm hne
    have p_dvd_an := p_dvd_a_p_sub_3 p hp_prime hp_ge_3
    rw [← a_explicit (p - 3)] at p_dvd_an
    have p_dvd_gcd : p ∣ Int.gcd m (a (p - 3)) := by
      apply Nat.dvd_gcd
      norm_cast
      apply Int.natCast_dvd.mp
      assumption
    simp_all
  -- 2. sufficiency
  · rintro ⟨i, ⟨_, rfl⟩⟩ n
    apply two_pow_gcd_one
