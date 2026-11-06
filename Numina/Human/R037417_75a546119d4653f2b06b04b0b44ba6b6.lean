import Mathlib
/- Find all $n$ natural numbers such that for each of them there exist $p , q$ primes such that these terms satisfy.

$1.$ $p+2=q$
$2.$ $2^n+p$ and $2^n+q$ are primes. -/
theorem number_theory_36363 (n : ℕ) : (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + 2 = q ∧ (2 ^ n + p).Prime ∧ (2 ^ n + q).Prime) ↔ n = 1 ∨ n = 3:= by
  constructor
  .
    -- Forward direction: if there exist primes p and q satisfying the conditions, then n=1 or n=3
    intro h
    rcases h with ⟨p, q, hp, hq, h, hp2, hq2⟩
    -- First we prove that p must be 3
    have h1 : p = 3:= by
      -- p cannot be 2
      have g1 : p ≠ 2:= by
        by_contra H
        subst p
        simp at h
        subst q
        absurd hq
        decide
      by_contra H
      -- p is greater than 1 (since it's prime)
      have g2 : p > 1:= by exact Nat.Prime.one_lt hp
      -- If p is not 3, then p > 3
      replace H : p > 3:= by omega
      clear g1 g2
      -- We'll show that p ≡ 2 (mod 3)
      have h1 : p ≡ 2 [MOD 3]:= by
        have g1 : Nat.Prime 3:= by decide
        mod_cases H1 : p % 3
        .
          -- Case: p ≡ 0 (mod 3)
          replace H1 : 3 ∣ p:= by exact Nat.dvd_of_mod_eq_zero H1
          replace H1 : 3 = p:= by exact (Nat.prime_dvd_prime_iff_eq g1 hp).mp H1
          linarith
        .
          -- Case: p ≡ 1 (mod 3)
          replace H1 : p + 2 ≡ 1 + 2 [MOD 3]:= by exact Nat.ModEq.add_right 2 H1
          rw [h] at H1
          simp at H1
          replace H1 : q ≡ 0 [MOD 3]:= by exact H1
          replace H1 : 3 ∣ q:= by exact Nat.dvd_of_mod_eq_zero H1
          replace H1 : 3 = q:= by exact (Nat.prime_dvd_prime_iff_eq g1 hq).mp H1
          linarith
        .
          -- Case: p ≡ 2 (mod 3)
          exact H1
      -- Rewrite as 2 ≡ p (mod 3)
      replace h1 : 2 ≡ p [MOD 3]:= by exact id (Nat.ModEq.symm h1)
      -- This means 3 divides p-2
      replace h1 : 3 ∣ p - 2:= by
        replace H : p ≥ 2:= by omega
        exact (Nat.modEq_iff_dvd' H).mp h1
      -- So p-2 = 3k for some k
      replace h1 : ∃ k : ℕ, p - 2 = 3 * k:= by exact h1
      rcases h1 with ⟨k, hk⟩
      -- Therefore p = 3k + 2
      replace hk : p = 3 * k + 2:= by omega
      -- We now consider two cases: n is odd or n is even
      by_cases hn : Odd n
      .
        -- Case: n is odd
        -- We'll show that 3 divides 2^n + q
        have h2 : 3 ∣ 2 ^ n + q:= by
          subst p q
          rw [show 2 ^ n + (3 * k + 2 + 2) = 2 ^ n + 1 + 3 * (k + 1) by ring]
          have g1 : 3 ∣ 3 * (k + 1):= by simp
          suffices 3 ∣ 2 ^ n + 1 by exact (Nat.dvd_add_iff_right this).mp g1
          zify
          suffices 2 ^ n + 1 ≡ 0 [ZMOD 3] by exact Int.dvd_of_emod_eq_zero this
          have g2 : 2 ≡ -1 [ZMOD 3]:= by rfl
          replace g2 : 2 ^ n ≡ (-1) ^ n [ZMOD 3]:= by exact Int.ModEq.pow n g2
          rw [show (-1 : ℤ) ^ n = -1 by exact Odd.neg_one_pow hn] at g2
          replace g2 : 2 ^ n + 1 ≡ -1 + 1 [ZMOD 3]:= by exact Int.ModEq.add g2 rfl
          rw [show (-1 : ℤ) + 1 = 0 by ring] at g2
          exact g2
        -- Since 2^n + q is prime and divisible by 3, it must equal 3
        have g1 : Nat.Prime 3:= by decide
        replace h2 : 3 = 2 ^ n + q:= by exact (Nat.prime_dvd_prime_iff_eq g1 hq2).mp h2
        have g2 : 2 ^ n > 0:= by positivity
        linarith
      .
        -- Case: n is even
        simp at hn
        -- We'll show that 3 divides 2^n + p
        have h2 : 3 ∣ 2 ^ n + p:= by
          subst p
          rw [show 2 ^ n + (3 * k + 2) = 2 ^ n + 2 + 3 * k by ring]
          have g1 : 3 ∣ 3 * k:= by simp
          suffices 3 ∣ 2 ^ n + 2 by exact (Nat.dvd_add_iff_right this).mp g1
          zify
          suffices 2 ^ n + 2 ≡ 0 [ZMOD 3] by exact Int.dvd_of_emod_eq_zero this
          have g2 : 2 ≡ -1 [ZMOD 3]:= by rfl
          replace g2 : 2 ^ n ≡ (-1) ^ n [ZMOD 3]:= by exact Int.ModEq.pow n g2
          rw [show (-1 : ℤ) ^ n = 1 by exact Even.neg_one_pow hn] at g2
          replace g2 : 2 ^ n + 2 ≡ 1 + 2 [ZMOD 3]:= by exact Int.ModEq.add g2 rfl
          rw [show (1 : ℤ) + 2 = 3 by ring] at g2
          exact g2
        -- Since 2^n + p is prime and divisible by 3, it must equal 3
        have g1 : Nat.Prime 3:= by decide
        replace h2 : 3 = 2 ^ n + p:= by exact (Nat.prime_dvd_prime_iff_eq g1 hp2).mp h2
        have g2 : 2 ^ n > 0:= by positivity
        linarith
    -- Now we know p = 3, so q = 5
    subst p
    simp at h
    subst q
    clear hp hq
    -- We'll prove that n = 1 or n = 3 by contradiction
    by_contra H
    simp at H
    -- First we show n ≠ 2
    have g1 : n ≠ 2:= by
      by_contra H1
      subst n
      simp at hq2
      absurd hq2
      decide
    -- And n ≠ 0
    have g2 : n ≠ 0:= by
      by_contra H1
      subst n
      simp at hp2
      absurd hp2
      decide
    -- So if n ≠ 1 and n ≠ 3, then n > 3
    replace g1 : n > 3:= by omega
    clear H g2
    -- We'll show that n must be odd
    have g2 : Odd n:= by
      by_contra H
      simp at H
      -- If n is even, we'll show that 3 divides 2^n + 5
      have h1 : 3 ∣ 2 ^ n + 5:= by
        zify
        suffices 2 ^ n + 5 ≡ 0 [ZMOD 3] by exact Int.dvd_of_emod_eq_zero this
        have g1 : 2 ≡ -1 [ZMOD 3]:= by rfl
        replace g1 : 2 ^ n ≡ (-1) ^ n [ZMOD 3]:= by exact Int.ModEq.pow n g1
        rw [show (-1 : ℤ) ^ n = 1 by exact Even.neg_one_pow H] at g1
        replace g1 : 2 ^ n + 5 ≡ 1 + 5 [ZMOD 3]:= by exact Int.ModEq.add g1 rfl
        rw [show (1 : ℤ) + 5 = 6 by ring] at g1
        exact g1
      -- Since 2^n + 5 is prime and divisible by 3, it must equal 3
      have g2 : Nat.Prime 3:= by decide
      replace h1 : 3 = 2 ^ n + 5:= by exact (Nat.prime_dvd_prime_iff_eq g2 hq2).mp h1
      have g3 : 2 ^ n > 0:= by positivity
      linarith
    -- So n is odd, which means n = 2k + 1 for some k
    simp [Odd] at g2
    rcases g2 with ⟨k, hk⟩
    -- We'll show that k must be odd
    have g2 : Odd k:= by
      by_contra H
      simp [Even] at H
      rcases H with ⟨r, hr⟩
      rw [show r + r = 2 * r by ring] at hr
      subst k
      rw [show 2 * (2 * r) + 1 = 4 * r + 1 by ring] at hk
      -- If k is even, we'll show that 5 divides 2^n + 3
      have h1 : 5 ∣ 2 ^ n + 3:= by
        subst n
        ring_nf
        rw [show r * 4 = 4 * r by ring]
        rw [show 2 ^ (4 * r) = (2 ^ 4) ^ r by exact Nat.pow_mul 2 4 r]
        simp
        suffices 3 + 16 ^ r * 2 ≡ 0 [MOD 5] by exact Nat.dvd_of_mod_eq_zero this
        have g2 : 16 ≡ 1 [MOD 5]:= by rfl
        replace g2 : 16 ^ r ≡ 1 ^ r [MOD 5]:= by exact Nat.ModEq.pow r g2
        simp at g2
        replace g2 : 16 ^ r * 2 ≡ 1 * 2 [MOD 5]:= by exact Nat.ModEq.mul g2 rfl
        simp at g2
        replace g2 : 3 + 16 ^ r * 2 ≡ 3 + 2 [MOD 5]:= by exact Nat.ModEq.add_left 3 g2
        rw [show 3 + 2 = 5 by ring] at g2
        exact g2
      -- Since 2^n + 3 is prime and divisible by 5, it must equal 5
      have g2 : Nat.Prime 5:= by decide
      replace h1 : 5 = 2 ^ n + 3:= by exact (Nat.prime_dvd_prime_iff_eq g2 hp2).mp h1
      replace g1 : 2 ^ n > 2 ^ 3:= by refine (Nat.pow_lt_pow_iff_right (by omega)).mpr g1
      linarith
    -- So k is odd, which means k = 2k1 + 1 for some k1
    simp [Odd] at g2
    rcases g2 with ⟨k1, hk1⟩
    subst k
    rw [show 2 * (2 * k1 + 1) + 1 = 4 * k1 + 3 by ring] at hk
    -- We'll show that 3 divides k1
    have h1 : 3 ∣ k1:= by
      mod_cases k1 % 3
      .
        -- Case: k1 ≡ 0 (mod 3)
        exact Nat.dvd_of_mod_eq_zero H
      .
        -- Case: k1 ≡ 1 (mod 3)
        -- We'll show that 7 divides 2^n + 5
        have g2 : 7 ∣ 2 ^ n + 5:= by
          subst n
          ring_nf
          rw [show k1 * 4 = 4 * k1 by ring]
          rw [show 2 ^ (4 * k1) = (2 ^ 4) ^ k1 by exact Nat.pow_mul 2 4 k1]
          simp
          replace H : 1 ≡ k1 [MOD 3]:= by exact id (Nat.ModEq.symm H)
          replace H : 3 ∣ k1 - 1:= by
            replace g1 : k1 ≥ 1:= by omega
            exact (Nat.modEq_iff_dvd' g1).mp H
          replace H : ∃ t : ℕ, k1 - 1 = 3 * t:= by exact H
          rcases H with ⟨t, ht⟩
          replace ht : k1 = 3 * t + 1:= by omega
          subst k1
          ring_nf
          rw [show t * 3 = 3 * t by ring]
          rw [show 16 ^ (3 * t) = (16 ^ 3) ^ t by exact Nat.pow_mul 16 3 t]
          simp
          suffices 5 + 4096 ^ t * 128 ≡ 0 [MOD 7] by exact Nat.dvd_of_mod_eq_zero this
          replace g1 : 4096 ≡ 1 [MOD 7]:= by rfl
          replace g1 : 4096 ^ t ≡ 1 ^ t [MOD 7]:= by exact Nat.ModEq.pow t g1
          simp at g1
          replace g1 : 4096 ^ t * 128 ≡ 1 * 128 [MOD 7]:= by exact Nat.ModEq.mul g1 rfl
          simp at g1
          replace g1 : 5 + 4096 ^ t * 128 ≡ 5 + 128 [MOD 7]:= by exact Nat.ModEq.add_left 5 g1
          rw [show 5 + 128 = 133 by ring] at g1
          exact g1
        -- Since 2^n + 5 is prime and divisible by 7, it must equal 7
        have g3 : Nat.Prime 7:= by decide
        replace h1 : 7 = 2 ^ n + 5:= by exact (Nat.prime_dvd_prime_iff_eq g3 hq2).mp g2
        replace g1 : 2 ^ n > 2 ^ 3:= by refine (Nat.pow_lt_pow_iff_right (by omega)).mpr g1
        linarith
      .
        -- Case: k1 ≡ 2 (mod 3)
        -- We'll show that 7 divides 2^n + 3
        have g2 : 7 ∣ 2 ^ n + 3:= by
          subst n
          ring_nf
          rw [show k1 * 4 = 4 * k1 by ring]
          rw [show 2 ^ (4 * k1) = (2 ^ 4) ^ k1 by exact Nat.pow_mul 2 4 k1]
          simp
          replace H : 2 ≡ k1 [MOD 3]:= by exact id (Nat.ModEq.symm H)
          replace g1 : k1 ≥ 2:= by
            by_contra H1
            simp at H1
            replace H1 : k1 = 1:= by omega
            subst k1
            simp [Nat.ModEq] at H
          replace H : 3 ∣ k1 - 2:= by exact (Nat.modEq_iff_dvd' g1).mp H
          replace H : ∃ t : ℕ, k1 - 2 = 3 * t:= by exact H
          rcases H with ⟨t, ht⟩
          replace ht : k1 = 3 * t + 2:= by omega
          subst k1
          ring_nf
          rw [show t * 3 = 3 * t by ring]
          rw [show 16 ^ (3 * t) = (16 ^ 3) ^ t by exact Nat.pow_mul 16 3 t]
          simp
          suffices 3 + 4096 ^ t * 2048 ≡ 0 [MOD 7] by exact Nat.dvd_of_mod_eq_zero this
          replace g1 : 4096 ≡ 1 [MOD 7]:= by rfl
          replace g1 : 4096 ^ t ≡ 1 ^ t [MOD 7]:= by exact Nat.ModEq.pow t g1
          simp at g1
          replace g1 : 4096 ^ t * 2048 ≡ 1 * 2048 [MOD 7]:= by exact Nat.ModEq.mul g1 rfl
          simp at g1
          replace g1 : 3 + 4096 ^ t * 2048 ≡ 3 + 2048 [MOD 7]:= by exact Nat.ModEq.add_left 3 g1
          rw [show 3 + 2048 = 2051 by ring] at g1
          exact g1
        -- Since 2^n + 3 is prime and divisible by 7, it must equal 7
        have g3 : Nat.Prime 7:= by decide
        replace h1 : 7 = 2 ^ n + 3:= by exact (Nat.prime_dvd_prime_iff_eq g3 hp2).mp g2
        replace g1 : 2 ^ n > 2 ^ 3:= by refine (Nat.pow_lt_pow_iff_right (by omega)).mpr g1
        linarith
    -- So k1 = 3l for some l
    replace h1 : ∃ l : ℕ, k1 = 3 * l:= by exact h1
    rcases h1 with ⟨l, hl⟩
    subst k1
    rw [show 4 * (3 * l) + 3 = 12 * l + 3 by ring] at hk
    -- We'll show that 13 divides 2^n + 5
    have h1 : 13 ∣ 2 ^ n + 5:= by
      subst n
      ring_nf
      rw [show l * 12 = 12 * l by ring]
      rw [show 2 ^ (12 * l) = (2 ^ 12) ^ l by exact Nat.pow_mul 2 12 l]
      simp
      suffices 5 + 4096 ^ l * 8 ≡ 0 [MOD 13] by exact Nat.dvd_of_mod_eq_zero this
      replace g1 : 4096 ≡ 1 [MOD 13]:= by rfl
      replace g1 : 4096 ^ l ≡ 1 ^ l [MOD 13]:= by exact Nat.ModEq.pow l g1
      simp at g1
      replace g1 : 4096 ^ l * 8 ≡ 1 * 8 [MOD 13]:= by exact Nat.ModEq.mul g1 rfl
      simp at g1
      replace g1 : 5 + 4096 ^ l * 8 ≡ 5 + 8 [MOD 13]:= by exact Nat.ModEq.add_left 5 g1
      rw [show 5 + 8 = 13 by ring] at g1
      exact g1
    -- Since 2^n + 5 is prime and divisible by 13, it must equal 13
    have g3 : Nat.Prime 13:= by decide
    replace h1 : 13 = 2 ^ n + 5:= by exact (Nat.prime_dvd_prime_iff_eq g3 hq2).mp h1
    replace g1 : 2 ^ n > 2 ^ 3:= by refine (Nat.pow_lt_pow_iff_right (by omega)).mpr g1
    linarith
  .
    -- Backward direction: if n=1 or n=3, then there exist primes p and q satisfying the conditions
    intro h
    rcases h with h | h
    all_goals
      subst n
      use 3, 5
      simp
      decide
