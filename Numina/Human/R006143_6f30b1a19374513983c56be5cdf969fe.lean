import Mathlib


/- if ab ≡ 0 (mod p), then a ≡ 0 (mod p) or b ≡ 0 (mod p)  -/
lemma Int.mul_modEq_zero_iff_of_prime {p: ℤ} {a b: ℤ}
  (pp: Prime p):
  a*b ≡ 0 [ZMOD p] ↔ (a ≡ 0 [ZMOD p] ∨ b ≡ 0 [ZMOD p]) := by
  simp only [Int.modEq_zero_iff_dvd, pp.dvd_mul]

/-  a ≡ b (mod n) iff a-b ≡ 0 (mod n) -/
lemma Int.modEq_iff_sub_modEq_zero {a b n: ℤ}:
  a ≡ b [ZMOD n] ↔ a - b ≡ 0 [ZMOD n] := by
  rw [Int.modEq_zero_iff_dvd, Int.modEq_comm,
  Int.modEq_iff_dvd]

/- Let $a$, $b$ be positive integers not exceeding $12$, satisfying:
there exists a constant $C$ such that ${{a}^{n}}+{{b}^{n+9}}\equiv C(\bmod 13)$ holds for any positive integer $n$.
Find all ordered pairs that satisfy the condition. -/
theorem number_theory_623031 {a b: ℕ} (apos: 0 < a) (bpos: 0 < b)
  (ale: a ≤ 12) (ble: b ≤ 12):
  ( ∃ C, ∀n, 0 < n → a^n + b^(n+9) ≡ C [MOD 13] ) ↔
  ( (a=1 ∧ b=1) ∨ (a=4 ∧ b=4) ∨ (a=10 ∧ b=10) ∨ (a=12 ∧ b=12) ) := by

  -- 13 is prime, and a,b are coprime to 13.
  have p13: Nat.Prime 13 := by norm_num
  have co_a: Nat.Coprime 13 a := Nat.coprime_of_lt_prime
    apos (Nat.lt_add_one_of_le ale) p13
  have co_b: Nat.Coprime 13 b := Nat.coprime_of_lt_prime
    bpos (Nat.lt_add_one_of_le ble) p13
  rw [Nat.coprime_comm] at co_a co_b

  -- by Fermat's little theorem, a^12, b^12 mod 13 is 1.
  have: 12 = Nat.totient 13 := by norm_num [Nat.totient_prime p13]
  have amod: a^12 ≡ 1 [MOD 13] := by
    simpa only [this] using (Nat.ModEq.pow_totient co_a)
  have bmod: b^12 ≡ 1 [MOD 13] := by
    simpa only [this] using (Nat.ModEq.pow_totient co_b)


  constructor

  · -- suppose exist such C
    rintro ⟨C, h⟩
    -- take n = 12, n = 12+3
    have h1 := h 12 (by norm_num)
    have h2 := h (12+3) (by norm_num)
    have h3 := h1.trans h2.symm
    -- a^12, b^12 mod 13 is 1, simplify
    replace h1: a^12 + b^(12+9) ≡ 1 + b^9 [MOD 13] := by
      refine amod.add ?_
      rw [← one_mul (b^9), pow_add]
      apply bmod.mul rfl
    replace h2: a^(12 + 3) + b^(12 + 3 + 9) ≡ a^3 + 1 [MOD 13] := by
      replace: a^(12 + 3) ≡ a^3 [MOD 13] := by
        rw [← one_mul (a^3), pow_add]
        apply amod.mul rfl
      refine this.add ?_
      rw [add_assoc, pow_add, ← mul_one 1]
      refine bmod.mul ?_
      norm_num [bmod]
    -- therefore b^9 mod 13 eq a^3
    replace h3: b^9 ≡ a^3 [MOD 13] := by
      replace: b^9 + 1 ≡ a^3 + 1 [MOD 13] := by
        rw [add_comm 1 _] at h1
        exact h1.symm.trans (h3.trans h2)
      exact this.add_right_cancel' 1
    -- then b^(n+9) mod 13 is a^3 times b^n.
    -- substitute back, simplify.
    have h4 {n:ℕ} (hn: 0 < n):
      (a^n - b^n) * (1-a^3) ≡ 0 [ZMOD 13] := by
      replace h1 := h n hn
      replace h1: a^n + b^n * a^3 ≡ C [MOD 13] := by
        symm; refine h1.symm.trans ?_
        apply Nat.ModEq.add rfl ?_
        rw [pow_add]
        apply Nat.ModEq.mul rfl h3
      replace h2 := h (n+3) (by linarith only [hn])
      replace h2: a^(n+3) + b^n ≡ C [MOD 13] := by
        symm; refine h2.symm.trans ?_
        apply Nat.ModEq.add rfl ?_
        rw [add_assoc, ← mul_one (b^n), pow_add]
        apply Nat.ModEq.mul rfl (by norm_num [bmod])
      replace := h1.trans h2.symm
      rw [← Int.natCast_modEq_iff, pow_add] at this
      push_cast at this
      replace h3: (a^n - b^n: ℤ) * (1 - a^3) =
        (a^n + b^n * a^3) - (a^n * a^3 + b^n) := by ring
      rwa [h3, ← Int.modEq_iff_sub_modEq_zero]
    replace h4 {n:ℕ} (hn: 0 < n):
      (a^n - b^n) ≡ 0 [ZMOD 13] ∨ (1 - a^3) ≡ 0 [ZMOD 13] := by
      rw [← Int.mul_modEq_zero_iff_of_prime (Int.prime_ofNat_iff.mpr p13)]
      exact h4 hn

    -- if n ≤ 12 and n^3 mod 13 is 1, then n = 1,3,9.
    have cube_modeq_1_case: ∀n, n ≤ 12 → 0 < n → n^3 ≡ 1 [MOD 13] →
      n = 1 ∨ n = 3 ∨ n = 9 := by decide
    -- if n^3 mod 13 is -1, n = 4,10,12.
    have cube_modeq_neg1_case: ∀n, n ≤ 12 → 0 < n →
      n^3 + 1 ≡ 0 [MOD 13] → n = 4 ∨ n = 10 ∨ n = 12 := by decide

    -- we will show if a^3 ≡ 1 (mod 13), then a,b = 1.
    have case_ab_eq_1 (ha: a^3 ≡ 1 [MOD 13]):
      a = 1 ∧ b = 1 := by
      have hb: b^3 ≡ 1 [MOD 13] := by
        replace := h3.trans ha
        replace: 1 * b^3 ≡ b^9 * b^3 [MOD 13] := by
          apply this.symm.mul rfl
        norm_num [← pow_add] at this
        exact this.trans bmod
      have aeq := cube_modeq_1_case a ale apos ha
      have beq := cube_modeq_1_case b ble bpos hb
      -- take n=1, n=3 at problem statement, a + b ≡ 2 mod 13.
      have hab: a + b ≡ 2 [MOD 13] := by
        replace h1 := h 1 (by norm_num)
        replace h2 := h 3 (by norm_num)
        replace h1: a + b ≡ C [MOD 13] := by
          apply Nat.ModEq.trans ?_ h1
          apply Nat.ModEq.add (by simp only [pow_one]; rfl) ?_
          nth_rw 1 [← mul_one b, pow_add]
          apply Nat.ModEq.mul (by simp only [pow_one]; rfl)
            (ha.symm.trans h3.symm)
        replace h2: 1 + 1 ≡ C [MOD 13] := by
          apply Nat.ModEq.trans ?_ h2
          apply Nat.ModEq.add ha.symm ?_
          norm_num [bmod.symm]
        exact (h1.trans h2.symm)
      -- so only case is a=1, b=1.
      clear * - aeq beq hab
      rcases aeq with (rfl | rfl | rfl)
      <;> rcases beq with (rfl | rfl | rfl)
      any_goals contradiction
      trivial

    -- consider whether a^3 mod 13 is 1
    by_cases ha: (1:ℤ) - a^3 ≡ 0 [ZMOD 13]
    · rw [← Int.modEq_iff_sub_modEq_zero] at ha
      replace ha: a^3 ≡ 1 [MOD 13] := by
        rw [← Int.natCast_modEq_iff]
        push_cast; exact ha.symm
      left; exact case_ab_eq_1 ha

    · -- a^n ≡ b^n case.
      simp only [ha, or_false,
      ← Int.modEq_iff_sub_modEq_zero] at h4
      -- take n = 1, a = b.
      replace h4: a = b := by
        specialize @h4 1 (by norm_num)
        have: (13:ℤ) = ↑(13:ℕ) := by simp
        rw [pow_one, pow_one, this,
        Int.natCast_modEq_iff] at h4
        replace: a % 13 = b := Nat.mod_eq_of_modEq h4
          (Nat.lt_add_one_of_le ble)
        rw [← this, Nat.mod_eq_of_lt (Nat.lt_add_one_of_le ale)]
      -- then a^3 mod 13 eq a^9
      rw [← h4, ← Int.natCast_modEq_iff,
      Int.modEq_iff_sub_modEq_zero] at h3
      push_cast at h3
      replace: (a^9:ℤ) - a^3 = a^3 * ( (a^3-1) * (a^3+1) ) := by ring
      rw [this, Int.mul_modEq_zero_iff_of_prime
        (Int.prime_ofNat_iff.mpr p13)] at h3
      replace: ¬ a^3 ≡ 0 [ZMOD 13] := by
        rintro heq
        replace: a^12 ≡ 0 [ZMOD 13] := by
          have hh1: (a^12:ℤ) = a^3 * a^9 := by ring
          have hh2: (0:ℤ) = 0 * a^9 := by simp
          rw [hh1, hh2]
          apply heq.mul rfl
        rw [← Int.natCast_modEq_iff] at amod
        push_cast at amod
        replace := this.symm.trans amod
        contradiction
      simp only [this, false_or, Int.mul_modEq_zero_iff_of_prime
        (Int.prime_ofNat_iff.mpr p13)] at h3
      -- now we obtain a^3 mod 13 is 1 or -1.
      rcases h3 with h3 | h3
      · rw [← Int.modEq_iff_sub_modEq_zero] at h3
        replace h3: a^3 ≡ 1 [MOD 13] := by
          rw [← Int.natCast_modEq_iff]
          simp [h3]
        -- a^3 mod 13 is 1, this case we already prove a=1, b=1.
        left; exact case_ab_eq_1 h3
      · replace h3: a^3 + 1 ≡ 0 [MOD 13] := by
          rw [← Int.natCast_modEq_iff]
          simp [h3]
        -- this case a = 4,10,12
        right
        specialize cube_modeq_neg1_case a ale apos h3
        simp [← h4, cube_modeq_neg1_case]


  · -- verification
    rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · use 2
      simp only [one_pow, Nat.reduceAdd]
      intro _ _; rfl
    all_goals
      use 0
      intro n hn
      rw [Nat.modEq_zero_iff_dvd]
      rw [pow_add, ← mul_one_add]
      apply Dvd.dvd.mul_left
      -- 13 divide 4^9 + 1, 10^9 + 1,12^9 + 1.
      -- since 4,10,12 all satisfy n^3 + 1 ≡ 0 (mod 13)
      -- so their cube mod 13 is -1, and therefore 9-th power also -1.
      norm_num