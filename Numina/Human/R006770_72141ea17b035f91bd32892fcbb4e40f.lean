import Mathlib

/-
Given an odd prime `p`, an integer `a ≥ 2` such that `p` does not divide `a` or `a-1`, prove that for every `k` with `1 ≤ k ≤ p`,
the expression `(a^{p!} - 1) / (a^k - 1)` is divisible by `p`.
-/

theorem prime_dvd_geom_quotient
  (hp : Nat.Prime p)
  (hp' : Odd p)
  (ha0 : a ≥ 2)
  (ha1 : ¬ p ∣ a)
  (ha2 : ¬ p ∣ (a - 1)) :
  ∀ k, 1 ≤ k → k ≤ p → p ∣ (a^(p.factorial)-1)/(a^k - 1) := by
  intro k hk₁ hk₂
  -- Step 1: Prove a^k - 1 divides a^{p!} - 1 since k | p!
  have h0 : (a^k - 1) ∣ (a^(p.factorial)-1) := by
    have r : k ∣ p.factorial := by
      exact Nat.dvd_factorial hk₁ hk₂
    obtain ⟨s, hs⟩ := r
    rw [hs, pow_mul]
    let b := a^k
    have hb : a^k = b := rfl
    simp [hb]
    refine (Nat.modEq_iff_dvd' ?_).mp ?_
    -- Show a^k ≥ 2 to ensure modulus is positive
    refine one_le_pow₀ ?_
    refine Nat.one_le_pow k a (by linarith)
    have r1 : 1 ≡ b [MOD b - 1] := by
      refine Nat.ModEq.symm (Nat.modEq_sub (by refine Nat.one_le_pow k a (by linarith)))
    have r2 : 1^s ≡ b^s [MOD b - 1] := by
      exact Nat.ModEq.pow s r1
    simp at r2
    exact r2

  -- Step 2: Apply Fermat's Little Theorem (a^{p-1} ≡ 1 mod p)
  have h1 : p ∣ a^(p-1) - 1 := by
    have t1 : (a : ℤ)^(p-1) ≡ 1 [ZMOD p] := by
      refine Int.ModEq.pow_card_sub_one_eq_one hp ?_
      refine IsCoprime.symm (Nat.Coprime.isCoprime ?_)
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr ha1
    refine (Nat.modEq_iff_dvd' ?_).mp ?_
    refine Nat.one_le_pow (p - 1) a (by omega)
    refine Int.natCast_modEq_iff.mp ?_
    simp
    exact id (Int.ModEq.symm t1)

  -- Step 3: p-1 divides p! since 1 < p-1 < p
  have h2 : p-1 ∣ p.factorial := by
    refine Nat.dvd_factorial ?_ ?_
    refine Nat.sub_pos_of_lt (by exact Nat.Prime.one_lt hp)
    omega

  -- Step 4: a^{p-1}-1 divides a^{p!}-1 by exponent lifting
  have h3 : a^(p-1) - 1 ∣ a^(p.factorial) - 1 := by
    obtain ⟨s, hs⟩ := h2
    rw [hs, pow_mul]
    let r := a^(p-1)
    have hr : a^(p-1) = r := rfl
    simp [hr]
    refine (Nat.modEq_iff_dvd' ?_).mp ?_
    refine one_le_pow₀ ?_
    refine Nat.one_le_pow (p - 1) a ?_
    linarith
    have r1 : 1 ≡ r [MOD r - 1] := by
      refine Nat.ModEq.symm (Nat.modEq_sub (by refine one_le_pow₀ (by linarith)))
    have r2 : 1^s ≡ r^s [MOD r - 1] := by
      exact Nat.ModEq.pow s r1
    simp at r2
    exact r2

  -- Step 5: p divides a^{p!}-1 by transitivity
  have h4 : p ∣ (a^(p.factorial)-1) := by
    exact Nat.dvd_trans h1 h3

  -- Case analysis on whether p divides a^k - 1
  by_cases h : ¬ p ∣ (a^k - 1)
  · -- Case 1: p does not divide a^k - 1 → must divide quotient
    by_contra h'
    have h'' : ¬ p ∣ (a ^ k - 1) * ((a ^ p.factorial - 1) / (a ^ k - 1)) := by
      exact Nat.Prime.not_dvd_mul hp h h'
    have h''' : (a ^ k - 1) * ((a ^ p.factorial - 1) / (a ^ k - 1)) = (a ^ p.factorial - 1) := by
      exact Nat.mul_div_cancel' h0
    rw [h'''] at h''
    tauto  -- Contradiction: p divides left side but not right

  · -- Case 2: p divides a^k - 1
    simp at h
    by_cases H : k = p
    · -- Subcase k = p: Derive contradiction since p would divide a-1
      have t1 : p ∣ a * (a^(p-1)-1) := by
        exact Dvd.dvd.mul_left h1 a
      have t2 : a * (a^(p-1)-1) = a^p - a := by
        have m1 : a ^ (p - 1) > 1 := by
          refine Nat.one_lt_pow ?_ ha0
          refine Nat.sub_ne_zero_iff_lt.mpr ?_
          exact Nat.Prime.one_lt hp
        have m2 : a * (a^(p-1)-1) = a^p - a := by
          have m3 : a * (a^(p-1)-1) = a * a^(p-1) - a := by
            exact Nat.mul_sub_one a (a ^ (p - 1))
          rw [m3]
          have m3 : a * a ^ (p - 1) = a ^ (p - 1) * a := by
            exact Nat.mul_comm a (a ^ (p - 1))
          have m4 : a ^ (p - 1) * a = a ^ (p - 1 + 1) := by
            exact rfl
          have m5 : a ^ (p - 1) * a = a^p := by
            refine Nat.pow_pred_mul (by exact Nat.Prime.pos hp)
          rw [m5] at m3
          exact Mathlib.Tactic.LinearCombination'.pf_sub_c m3 a  -- Algebra: a * a^{p-1} = a^p
        exact m2
      rw [H] at h  -- Now h: p ∣ a^p - 1
      have t3 : p ∣ ((a^p - 1) - (a^p - a)) := by
        refine Nat.dvd_sub' h (by exact (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod t2) (a ^ (p - 1) - 1)) h1).mp t1)
      have t4 : ((a^p - 1) - (a^p - a)) = a - 1 := by
        have m1 : a > 1 := by
          exact ha0
        have m2 : (a^p - 1) > (a^p - a) := by
          refine Nat.sub_lt_sub_left (by refine Nat.one_lt_pow (by exact Nat.Prime.ne_zero hp) ha0) ha0
        have m3 : a^p > 1 := by
          refine Nat.one_lt_pow (by exact Nat.Prime.ne_zero hp) ha0
        have m4 : a^p > a := by
          refine lt_self_pow₀ ha0 (by exact Nat.Prime.one_lt hp)
        omega  -- Linear arithmetic finishes
      rw [t4] at t3
      tauto  -- Contradicts hypothesis ¬ p ∣ a-1

    · -- Subcase k < p: Express quotient as geometric series
      have r0 : k < p := by
        omega
      have r1 : p.factorial = p * (p-1).factorial := by
        refine Eq.symm (Nat.mul_factorial_pred (by exact Nat.zero_lt_of_lt r0))
      have r2 : k ∣ (p-1).factorial := by
        refine Nat.dvd_factorial hk₁ (by omega)
      obtain ⟨s, hs⟩ := r2
      have r3 : p.factorial = k * (p * s) := by
        rw [r1, hs]; ring
      rw [r3, pow_mul]
      let b := a^k
      have hb : a^k = b := rfl
      simp [hb]
      -- Prove b ≥ 2 for geometric series formula
      have hbpos : b ≥ 2 := by
        rw [← hb]
        simp
        have t1 : 2 ≤ a := by
          exact ha0
        have t3 : 0 < 2 := by
          simp
        have t4 : 2 ≤ 2^k := by
          exact Nat.pow_le_pow_of_le_right t3 hk₁
        have t5 : 2^k ≤ a^k := by
          exact Nat.pow_le_pow_of_le_left ha0 k
        exact Nat.le_trans t4 t5

      -- Prove b ≡ 1 mod p (using h: p ∣ b - 1)
      have hb1 : b ≡ 1 [MOD p] := by
        rw [Nat.modEq_iff_dvd]
        rw [hb] at h
        have t1 : p ≥ 1 := by
          omega
        have t2 : b - 1 ≥ 1 := by
          exact Nat.le_sub_one_of_lt hbpos
        set w : ℕ := b - 1 with hw
        have t3 : (p : ℤ) ∣ (w : ℤ) := by
          exact Int.ofNat_dvd.mpr h
        have t4 : (w : ℤ) = ((b : ℤ) - 1) := by
          omega
        rw [t4] at t3
        exact dvd_sub_comm.mp t3  -- Convert integer divisibility to natural number

      -- Express quotient as geometric series ∑_{i=0}^{p*s-1} b^i
      have h_sum : (b^(p*s) - 1) / (b - 1) = ∑ i in Finset.range (p*s), b^i := by
        exact Eq.symm (Nat.geomSum_eq hbpos (p * s))

      rw [h_sum]
      rw [Nat.dvd_iff_mod_eq_zero]  -- Goal: (∑ b^i) % p = 0

      -- Show each b^i ≡ 1 mod p → sum ≡ p*s * 1 mod p ≡ 0 mod p
      have : (∑ i in Finset.range (p*s), b^i) % p = (∑ i in Finset.range (p*s), 1) % p := by
        rw [Finset.sum_nat_mod]  -- Push modulus into sum
        congr  -- Prove sums equal mod p by showing term-wise equality
        ext i
        have hb2 : b % p = 1 := by
          refine Nat.mod_eq_of_modEq hb1 ?hb  -- Extract b mod p = 1
          omega
        have t1 : b^i % p = (b % p)^i % p := by
          exact Nat.pow_mod b i p
        have t2 : 1 < p := by
          omega
        rw [t1, hb2]
        simp
        exact Nat.mod_eq_of_lt t2  -- 1^i % p = 1, and 1 < p

      rw [this, Finset.sum_const, nsmul_eq_mul, Finset.card_range]  -- ∑ 1 = p * s
      simp [Nat.mul_mod_right]  -- (p * s) % p = 0
