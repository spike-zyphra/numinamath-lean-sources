import Mathlib

/--
**Theorem:** Let `K ≥ 3` be an integer. Let `N₀` be the least positive integer `N`
such that `2^K` divides `m^N - 1` for every odd integer `m > 1`.
Then `N₀ = 2^(K-2)`.
-/
theorem least_exponent_is_pow_two (K : ℕ) (hK : 3 ≤ K) : sInf { N | 0 < N ∧ (∀ m : ℕ, 1 < m → Odd m → 2 ^ K ∣ m ^ N - 1) } = 2 ^ (K - 2) := by
  -- The proof proceeds by showing N₀ ≤ 2^(K-2) and 2^(K-2) ≤ N₀.

  -- Basic Facts
  have h_2_dvd_pow_2: 2 ∣ 2 ^ (K - 2) := by exact Dvd.dvd.pow (by decide) (by omega)

  have h_pow_ge: 2 ≤ 2 ^ (K - 2) :=by refine Nat.le_self_pow (by omega) 2

  have h_prime_2: Prime 2 := Nat.prime_iff.mp (by decide)

  -- Part 1: N₀ ≤ 2^(K-2)
  have part_1: ∀ m : ℕ, 1 < m → Odd m → 2 ^ K ∣ m ^ 2 ^ (K - 2) - 1 := by
    intro m hm_gt_one hm_odd
    -- We must handle m being negative, though the problem says m > 1.
    -- The property `part_i` holds for all odd integers m.

    have : m ≥ 2 := by omega

    have : m ^ 2 ^ (K - 2) ≥ 4:= by
      calc
        _ ≥ m ^ 2 := Nat.pow_le_pow_of_le hm_gt_one h_pow_ge
        _ = m * m := by ring
        _ ≥ 2 * 2 := by nlinarith
        _ = 4 := by omega

    -- square of odd is 1 mod 4
    have h_mod_4: m ^ 2 = (1: ZMod 4) := by
      have : (m : ℤ) ^ 2 % 4 = 1 % 4 := Int.sq_mod_four_eq_one_of_odd (by norm_cast: Odd (m:ℤ))
      have cast_mod4 := (ZMod.intCast_eq_intCast_iff' (m ^ 2) 1 4).mpr this
      norm_num at cast_mod4
      exact cast_mod4

    have : 1 + (K - 3) = K - 2 := by omega

    have h_pow_mod_4: (m: ZMod 4) ^ 2 ^ (K - 2) = (1: ZMod 4) := by
      calc
        _ = (m: ZMod 4) ^ (2 * 2 ^ (K - 3)) := by
          congr
          nth_rw 3 [← pow_one 2]
          rw [← pow_add]
          congr
          omega
        _ = ((m: ZMod 4) ^ 2) ^ (2 ^ (K - 3)):= by rw [pow_mul]
        _ = (1: ZMod 4) := by simp [h_mod_4]

    -- m^2 - 1 is divisible by 4
    have h_4_dvd_pow: 4 ∣ m ^ 2 ^ (K - 2) - 1 := by
      have : (m ^ 2 ^ (K - 2) -1: ℕ) = (0: ZMod 4) := by
        have zmod_eq_zero:= sub_eq_zero.mpr h_pow_mod_4
        rw [Nat.cast_sub]
        norm_num
        simp [sub_eq_zero]
        exact h_pow_mod_4
        omega

      exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp this

    -- m is odd, so m - 1 is even
    have h_2_not_dvd_m : ¬2 ∣ m := Odd.not_two_dvd_nat hm_odd

    have h_2_dvd_pow: 2 ∣ m - 1 := by
      have : m % 2 = 1:= Nat.two_dvd_ne_zero.mp h_2_not_dvd_m
      have : (m - 1) % 2 = 0 := Nat.sub_mod_eq_zero_of_mod_eq this
      exact Nat.dvd_of_mod_eq_zero this

    have h_even_pow_2: Even (2 ^ (K - 2)) := by exact
      (even_iff_exists_two_nsmul (2 ^ (K - 2))).mpr h_2_dvd_pow_2

    -- LTE equation
    have lte_eq : padicValNat 2 (m ^ 2 ^ (K - 2) - 1 ^ 2 ^ (K - 2)) + 1 =
padicValNat 2 (m + 1) + padicValNat 2 (m - 1) + padicValNat 2 (2 ^ (K - 2)) := padicValNat.pow_two_sub_pow (by omega) h_2_dvd_pow h_2_not_dvd_m (by omega) h_even_pow_2

    -- padic valuation of 2^K-2
    have h_emul_2 : padicValNat 2 (2 ^ (K - 2)) = K - 2 := padicValNat.prime_pow (K - 2)

    -- padic valuation of 8
    have h_emul_2_8 : padicValNat 2 8 = 3 := by
      rw [show 8 = 2^3 by omega]
      exact padicValNat.prime_pow 3

    -- since m is odd, m = 2k + 1 for some k
    rcases hm_odd with ⟨k, hk⟩
    rcases Nat.even_mul_succ_self k with ⟨j, hj⟩

    -- square of odd is 1 mod 8
    have h_m_eq_8j: m^2 - 1 = 8 * j := by
      calc
        _ = (2 * k + 1)^2 - 1 := by rw [hk]
        _ = 4 * (k * (k + 1)) := by ring_nf; omega
        _ = 4 * (j + j) := by congr
        _ = 8 * j := by ring

    -- j is not zero
    have h_j_ne_zero: j ≠ 0 := by
      by_contra h_absurd
      have h_absurd_1: m^2 - 1 = 0 := by
        calc
          _ = 8 * j := by rw [h_m_eq_8j]
          _ = 0 := by omega
      have h_absurd_2: m^2 ≥ 4 := by
        calc
          _ = m * m := by ring
          _ ≥ 2 * 2 := by nlinarith

      omega


    -- derive equality from the LTE equation
    have adic_2_eq: padicValNat 2 (m ^ 2 ^ (K - 2) - 1) + 1 = padicValNat 2 j + K + 1 := by
      calc
        _ = padicValNat 2 (m ^ 2 ^ (K - 2) - 1 ^ 2 ^ (K - 2)) + 1 := by simp
        _ = padicValNat 2 (m + 1) + padicValNat 2 (m - 1) + padicValNat 2 (2 ^ (K - 2)) := by rw [lte_eq]
        _ = padicValNat 2 (m + 1) + padicValNat 2 (m - 1) + (K - 2) := by simp [h_emul_2]
        _ = padicValNat 2 (m^2 - 1) + (K - 2) := by
          have h_sq_sub_sq : m^2 - 1 = (m + 1)*(m - 1):= by exact Nat.sq_sub_sq m 1
          rw [h_sq_sub_sq]
          have: padicValNat 2 ((m + 1)*(m - 1)) = padicValNat 2 (m + 1) + padicValNat 2 (m - 1):= padicValNat.mul (by omega) (by omega)
          simp [this]
        _ = padicValNat 2 (8 * j) + (K - 2) := by rw [h_m_eq_8j]
        _ = padicValNat 2 8 + padicValNat 2 j + (K - 2) := by
          have: padicValNat 2 (8 * j) = padicValNat 2 8 + padicValNat 2 j := padicValNat.mul (by omega) (by omega)
          simp [this]
        _ = padicValNat 2 j + K + 1 := by simp [h_emul_2_8]; omega

    -- derive bound on 2-adic valuation of m ^ 2 ^ (K - 2) - 1
    have adic_2_ineq: padicValNat 2 (m ^ 2 ^ (K - 2) - 1) ≥ K := by omega

    exact (padicValNat_dvd_iff_le (by omega)).mpr adic_2_ineq


  apply Nat.le_antisymm
  · -- Proof of N₀(K) ≤ 2^(K-2).
    -- This follows from showing that 2^(K-2) has the property P.
    apply Nat.sInf_le
    constructor
    · positivity
    ·
      exact part_1

  · -- Proof of 2^(K-2) ≤ N₀(K).
    -- We use the properties of the group exponent (Carmichael function).
    -- The set {N | P K N} is the set of multiples of the exponent of (ℤ/2^Kℤ)ˣ.
    -- N₀(K) is the exponent of this group.

    let N_K := sInf { N | 0 < N ∧ (∀ m : ℕ, 1 < m → Odd m → 2 ^ K ∣ m ^ N - 1) }
    have h_N_K_nonempty : { N | 0 < N ∧ (∀ m : ℕ, 1 < m → Odd m → 2 ^ K ∣ m ^ N - 1) }.Nonempty := by
      apply Set.nonempty_def.mpr
      use 2^(K-2)
      constructor
      · positivity
      · exact part_1

    have h_N_K : 0 < N_K ∧ (∀ m : ℕ, 1 < m → Odd m → 2 ^ K ∣ m ^ N_K - 1) := by
      exact Nat.sInf_mem h_N_K_nonempty

    have h_N_K_ge_1: 3^N_K ≥ 3 :=by refine Nat.le_self_pow (by omega) 3

    have h_N_K_prop : ∀ m : ℕ, 1 < m → Odd m → 2 ^ K ∣ m ^ N_K - 1:= h_N_K.2


    -- For `m=3`, `2^K` does not divide `3^(2^(K-3)) - 1`.
    -- This serves as a counterexample for any exponent that is a power of two smaller
    -- than `2^(K-2)`.

    have h_example_3 : 2 ^ K ∣ 3 ^ N_K - 1 := h_N_K_prop 3 (by norm_num) (by decide)

    -- derive inequality on 2-adic valuation of 3 ^ N_K - 1
    have h_example_3_ineq: padicValNat 2 (3 ^ N_K - 1) ≥ K := (padicValNat_dvd_iff_le (by omega)).mp h_example_3

    have : 3 ^ 2 ^ (K - 2) ≥ 9:= by
      calc
        _ ≥ 3 ^ 2 := Nat.pow_le_pow_of_le (by omega) h_pow_ge
        _ = 9 := by omega

    have h_mod_4: 3 ^ 2 = (1: ZMod 4) := by decide

    have : 1 + (K - 3) = K - 2 := by omega

    have h_pow_mod_4: (3: ZMod 4) ^ 2 ^ (K - 2) = (1: ZMod 4) := by
      calc
        _ = (3: ZMod 4) ^ (2 * 2 ^ (K - 3)) := by
          congr
          nth_rw 3 [← pow_one 2]
          rw [← pow_add]
          congr
          omega
        _ = ((3: ZMod 4) ^ 2) ^ (2 ^ (K - 3)):= by rw [pow_mul]
        _ = (1: ZMod 4) := by simp [h_mod_4]

    -- deduce that 3 ^ 2 ^ (K - 2) - 1 is divisible by 4
    have h_4_dvd_pow: 4 ∣ 3 ^ 2 ^ (K - 2) - 1 := by
      have : (3 ^ 2 ^ (K - 2) -1: ℕ) = (0: ZMod 4) := by
        have zmod_eq_zero:= sub_eq_zero.mpr h_pow_mod_4
        rw [Nat.cast_sub]
        norm_num
        simp [sub_eq_zero]
        exact h_pow_mod_4
        omega

      exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp this

    have h_2_dvd_pow: 2 ∣ 3 - 1 := by decide

    -- show that N_K must be even
    have h_even_pow_2: Even N_K := by
      -- prove by contradiction
      -- Suppose N_K is odd
      by_contra h_absurd


      have h_absurd_1: ¬(2:ℤ) ∣ N_K:= by
        contrapose
        simp
        norm_cast
        exact Nat.not_even_iff.mp h_absurd

      -- Use LTE to derive an equation involving the 2-adic valuation of 3 ^ N_K - 1
      have lte := emultiplicity_pow_sub_pow_of_prime Int.prime_two (by decide:  (2:ℤ)∣ 3 - 1) (by decide: ¬ (2:ℤ) ∣ 3) h_absurd_1

      simp at lte

      -- 2-adic valuation of 2
      have : emultiplicity (2:ℤ) (2:ℤ) = 1:= by
        refine FiniteMultiplicity.emultiplicity_self ?_
        refine FiniteMultiplicity.of_prime_left ?_ ?_
        . exact Int.prime_two
        . omega

      rw [this] at lte

      -- derive contradiction
      have: (1: ℕ∞) ≥ 3:= by
        calc
          _ = emultiplicity (2:ℤ) (3 ^ N_K - 1) := lte.symm
          _ ≥ K := by
            apply pow_dvd_iff_le_emultiplicity.mp
            zify at h_example_3
            norm_num at h_example_3
            exact h_example_3
          _ ≥ 3 := Nat.ofNat_le_cast.mpr hK

      norm_num at this

    -- Use LTE to derive an equation involving the 2-adic valuation of 3 ^ N_K - 1
    have lte_eq : padicValNat 2 (3 ^ N_K - 1 ^ N_K) + 1 =
padicValNat 2 (3 + 1) + padicValNat 2 (3 - 1) + padicValNat 2 N_K := padicValNat.pow_two_sub_pow (by omega) h_2_dvd_pow (by decide) (by omega) h_even_pow_2

    -- derive inequality on 2-adic valuation of N_K
    have adic_2_ineq: K + 1 ≤ padicValNat 2 N_K + 3 := by
      calc
        _ ≤ padicValNat 2 (3 ^ N_K - 1 ^ N_K) + 1 := by simp [h_example_3_ineq]
        _ = padicValNat 2 (3 + 1) + padicValNat 2 (3 - 1) + padicValNat 2 N_K := by rw [lte_eq]
        _ = 2 + 1 + padicValNat 2 N_K := by
          have h_3_plus_1: padicValNat 2 (3 + 1)=2 := by
            rw [(show 3 + 1 = 2 ^ 2 by omega)]
            exact padicValNat.prime_pow 2
          have h_3_minus_1: padicValNat 2 (3 - 1)=1 := by
            rw [(show 3 - 1 = 2 by omega)]
            simp [padicValNat.prime_pow]
          rw [h_3_plus_1, h_3_minus_1]
        _ = padicValNat 2 N_K + 3 := by omega

    -- derive bounds on 2-adic valuation of N_K
    have adic_2_ineq' :padicValNat 2 N_K ≥ K - 2 := by omega

    -- this gives a lower bound on N_K
    have : 2 ^ (K - 2) ∣ N_K := (padicValNat_dvd_iff_le (by omega)).mpr adic_2_ineq'

    have h_N_K_ge_pow_2: 2 ^ (K - 2) ≤ N_K := Nat.le_of_dvd (by omega) this

    exact h_N_K_ge_pow_2
