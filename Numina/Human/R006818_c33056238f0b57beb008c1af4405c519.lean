import Mathlib
/- Let $k$ be a positive integer such that $\gcd(k,6)=1$. Show that the integer $2^k-1$ is not divisible by any prime number less than $10$. -/
theorem number_theory_641440 (k : ℕ) (hk : Nat.gcd k 6 = 1) : ∀ p : ℕ, Nat.Prime p ∧ p < 10 → ¬(p ∣ 2 ^ k - 1):= by
  intro p ⟨hp, h⟩
  -- First, prove that p must be 2, 3, 5, or 7 (the only primes less than 10)
  replace h : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7:= by
    by_cases hp1 : p = 2
    .
      omega
    .
      -- If p ≠ 2, then p must be odd
      replace hp1 : Odd p:= by exact Nat.Prime.odd_of_ne_two hp hp1
      -- Since p is prime, it must be greater than 1
      have hp2 : p > 1:= by exact Nat.Prime.one_lt hp
      rcases hp1 with ⟨n, hn⟩
      subst p
      -- n must be 1, 2, 3, or 4 to make p < 10
      replace h : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4:= by omega
      rcases h with h | h | h | h
      all_goals
        subst n
        simp
      simp at hp
      absurd hp
      decide
  -- Prove k ≠ 0 using the gcd condition
  have hk1 : k ≠ 0:= by
    by_contra H
    subst k
    simp at hk
  -- Handle each prime case separately
  rcases h with h | h | h | h
  .
    -- Case p = 2: Show 2^k - 1 is odd
    subst p
    suffices Odd (2 ^ k - 1) by exact Odd.not_two_dvd_nat this
    have g1 : Even (2 ^ k):= by refine (Nat.even_pow' hk1).mpr (by decide)
    refine Nat.Even.sub_odd (by linarith [show 2 ^ k > 0 by positivity]) g1 (by decide)
  .
    -- Case p = 3: Use modular arithmetic to show 3 doesn't divide 2^k - 1
    subst p
    zify
    by_contra H
    field_simp at H
    replace H : 2 ^ k ≡ 1 [ZMOD 3]:= by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) H)
    have g1 : 2 ≡ -1 [ZMOD 3]:= by rfl
    replace g1 : 2 ^ k ≡ (-1) ^ k [ZMOD 3]:= by exact Int.ModEq.pow k g1
    -- Prove k is odd using the gcd condition
    have hk2 : Odd k:= by
      by_contra H1
      simp at H1
      replace H1 : 2 ∣ k:= by exact even_iff_two_dvd.mp H1
      have H2 : 2 ∣ 6:= by omega
      replace H1 : 2 ∣ 1:= by rw [←hk] ; exact Nat.dvd_gcd H1 H2
      omega
    rw [show (-1) ^ k = -1 by exact Odd.neg_one_pow hk2] at g1
    replace H : 1 ≡ -1 [ZMOD 3]:= by exact Int.ModEq.trans (id (Int.ModEq.symm H)) g1
    replace H : 3 ∣ (1 : ℤ) - (-1):= by exact Int.ModEq.dvd (id (Int.ModEq.symm H))
    simp at H
    omega
  .
    -- Case p = 5: Use modular arithmetic and case analysis on k mod 4
    subst p
    zify
    field_simp
    by_contra H
    replace H : 2 ^ k ≡ 1 [ZMOD 5]:= by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) H)

    -- Prove k ≥ 3 using the gcd condition
    have g1 : k ≥ 3:= by
      by_contra H2
      replace H2 : k = 1 ∨ k = 2:= by omega
      rcases H2 with H2 | H2
      all_goals
        subst k
        simp [Int.ModEq] at H
    -- Case analysis on k mod 4
    mod_cases H1 : k % 4
    .
      -- Case k ≡ 0 (mod 4)
      replace H1 : 4 ∣ k:= by exact Nat.dvd_of_mod_eq_zero H1
      rcases H1 with ⟨q, hq⟩
      subst k
      have g1 : 2 ∣ 4 * q:= by omega
      have g2 : 2 ∣ 6:= by omega
      replace g1 : 2 ∣ 1:= by rw [←hk] ; exact Nat.dvd_gcd g1 g2
      omega
    .
      -- Case k ≡ 1 (mod 4)
      replace H1 : 4 ∣ k - 1:= by refine (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm H1))
      rcases H1 with ⟨q, hq⟩
      replace hq : k = 4 * q + 1:= by omega
      subst k
      ring_nf at H
      rw [show q * 4 = 4 * q by omega] at H
      rw [show (2 : ℤ) ^ (4 * q) = (2 ^ 4) ^ q by exact pow_mul 2 4 q] at H
      simp at H
      have g1 : 16 ≡ 1 [ZMOD 5]:= by rfl
      replace g1 : 16 ^ q ≡ 1 ^ q [ZMOD 5]:= by exact Int.ModEq.pow q g1
      simp at g1
      replace g1 : 16 ^ q * 2 ≡ 1 * 2 [ZMOD 5]:= by exact Int.ModEq.mul g1 rfl
      simp at g1
      replace H : 2 ≡ 1 [ZMOD 5]:= by exact Int.ModEq.trans (id (Int.ModEq.symm g1)) H
      simp [Int.ModEq] at H
    .
      -- Case k ≡ 2 (mod 4)
      replace H1 : 4 ∣ k - 2:= by refine (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm H1))
      rcases H1 with ⟨q, hq⟩
      replace hq : k = 4 * q + 2:= by omega
      subst k
      ring_nf at H
      rw [show q * 4 = 4 * q by omega] at H
      rw [show (2 : ℤ) ^ (4 * q) = (2 ^ 4) ^ q by exact pow_mul 2 4 q] at H
      simp at H
      have g1 : 16 ≡ 1 [ZMOD 5]:= by rfl
      replace g1 : 16 ^ q ≡ 1 ^ q [ZMOD 5]:= by exact Int.ModEq.pow q g1
      simp at g1
      replace g1 : 16 ^ q * 4 ≡ 1 * 4 [ZMOD 5]:= by exact Int.ModEq.mul g1 rfl
      simp at g1
      replace H : 4 ≡ 1 [ZMOD 5]:= by exact Int.ModEq.trans (id (Int.ModEq.symm g1)) H
      simp [Int.ModEq] at H
    .
      -- Case k ≡ 3 (mod 4)
      replace H1 : 4 ∣ k - 3:= by refine (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm H1))
      rcases H1 with ⟨q, hq⟩
      replace hq : k = 4 * q + 3:= by omega
      subst k
      ring_nf at H
      rw [show q * 4 = 4 * q by omega] at H
      rw [show (2 : ℤ) ^ (4 * q) = (2 ^ 4) ^ q by exact pow_mul 2 4 q] at H
      simp at H
      have g1 : 16 ≡ 1 [ZMOD 5]:= by rfl
      replace g1 : 16 ^ q ≡ 1 ^ q [ZMOD 5]:= by exact Int.ModEq.pow q g1
      simp at g1
      replace g1 : 16 ^ q * 8 ≡ 1 * 8 [ZMOD 5]:= by exact Int.ModEq.mul g1 rfl
      simp at g1
      replace H : 8 ≡ 1 [ZMOD 5]:= by exact Int.ModEq.trans (id (Int.ModEq.symm g1)) H
      simp [Int.ModEq] at H
  .
    -- Case p = 7: Use modular arithmetic and case analysis on k mod 3
    subst p
    zify
    field_simp
    by_contra H
    replace H : 2 ^ k ≡ 1 [ZMOD 7]:= by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) H)
    -- Case analysis on k mod 3
    mod_cases H1 : k % 3
    .
      -- Case k ≡ 0 (mod 3)
      replace H1 : 3 ∣ k:= by exact Nat.dvd_of_mod_eq_zero H1
      rcases H1 with ⟨q, hq⟩
      subst k
      have g1 : 3 ∣ 3 * q:= by omega
      have g2 : 3 ∣ 6:= by omega
      replace g1 : 3 ∣ 1:= by rw [←hk] ; exact Nat.dvd_gcd g1 g2
      omega
    .
      -- Case k ≡ 1 (mod 3)
      replace H1 : 3 ∣ k - 1:= by refine (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm H1))
      rcases H1 with ⟨q, hq⟩
      replace hq : k = 3 * q + 1:= by omega
      subst k
      ring_nf at H
      rw [show q * 3 = 3 * q by omega] at H
      rw [show (2 : ℤ) ^ (3 * q) = (2 ^ 3) ^ q by exact pow_mul 2 3 q] at H
      simp at H
      have g1 : 8 ≡ 1 [ZMOD 7]:= by rfl
      replace g1 : 8 ^ q ≡ 1 ^ q [ZMOD 7]:= by exact Int.ModEq.pow q g1
      simp at g1
      replace g1 : 8 ^ q * 2 ≡ 1 * 2 [ZMOD 7]:= by exact Int.ModEq.mul g1 rfl
      simp at g1
      replace H : 2 ≡ 1 [ZMOD 7]:= by exact Int.ModEq.trans (id (Int.ModEq.symm g1)) H
      simp [Int.ModEq] at H
    .
      -- Case k ≡ 2 (mod 3)
      have hk2 : k ≠ 1:= by
        by_contra H
        subst k
        simp [Int.ModEq] at H
      replace H1 : 3 ∣ k - 2:= by refine (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm H1))
      rcases H1 with ⟨q, hq⟩
      replace hq : k = 3 * q + 2:= by omega
      subst k
      ring_nf at H
      rw [show q * 3 = 3 * q by omega] at H
      rw [show (2 : ℤ) ^ (3 * q) = (2 ^ 3) ^ q by exact pow_mul 2 3 q] at H
      simp at H
      have g1 : 8 ≡ 1 [ZMOD 7]:= by rfl
      replace g1 : 8 ^ q ≡ 1 ^ q [ZMOD 7]:= by exact Int.ModEq.pow q g1
      simp at g1
      replace g1 : 8 ^ q * 4 ≡ 1 * 4 [ZMOD 7]:= by exact Int.ModEq.mul g1 rfl
      simp at g1
      replace H : 4 ≡ 1 [ZMOD 7]:= by exact Int.ModEq.trans (id (Int.ModEq.symm g1)) H
      simp [Int.ModEq] at H
