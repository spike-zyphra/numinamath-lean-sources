import Mathlib
/- Let $b$ be an integer such that $b \ge 2$ and $b \equiv 3 \pmod 4$. Define the sequence of positive integers $a_k$ recursively by $a_1=b$ and $a_k=b^{a_{k-1}}$ for all $k \ge 2$. Let $N$ be an integer such that $N \ge 3$. Show that the last two digits of $a_N$ are $b^{(b^3 \pmod{20})} \pmod{100}$. -/
theorem number_theory_637775 (b : ℕ) (hb : b ≥ 2) (h : b ≡ 3 [MOD 4]) (a : ℕ → ℕ) (ha1 : a 1 = b) (ha : ∀ n : ℕ, a (n + 2) = b ^ a (n + 1)) : ∀ n : ℕ, n ≥ 3 → a n % 100 = b ^ (b ^ 3 % 20) % 100:= by
  replace hb : b ≥ 3:= by
    by_contra H
    replace H : b = 2:= by omega
    rw [H] at h
    simp [Nat.ModEq] at h
  -- Prove that all terms a_{n+1} ≡ 3 (mod 4) by induction
  have h1 : ∀ n : ℕ, a (n + 1) ≡ 3 [MOD 4]:= by
    intro n
    induction n with
    | zero =>
      -- Base case: a_1 = b ≡ 3 (mod 4)
      simp
      rw [ha1]
      exact h
    | succ n ih =>
      -- Inductive step: a_{n+2} = b^(a_{n+1}) ≡ 3 (mod 4)
      rw [ha n]
      -- First prove that a_{n+1} is odd
      have hOdd : Odd (a (n + 1)):= by
        -- Prove that b is odd since b ≡ 3 (mod 4)
        have hOdd : Odd b:= by
          replace h : 4 ∣ b - 3:= by exact (Nat.modEq_iff_dvd' hb).mp (id (Nat.ModEq.symm h))
          rcases h with ⟨k, hk⟩
          replace hk : b = 4 * k + 3:= by omega
          use (2 * k + 1)
          linarith
        by_cases hn : n = 0
        .
          -- If n = 0, then a_{n+1} = a_1 = b, which is odd
          subst n
          simp
          rw [ha1]
          exact hOdd
        .
          -- If n > 0, then a_{n+1} = b^(a_n), which is odd since b is odd
          set n1:= n - 1 with hn1
          clear_value n1
          replace hn1 : n = n1 + 1:= by omega
          subst n
          rw [ha n1]
          exact Odd.pow hOdd
      -- Now prove that b^(a_{n+1}) ≡ 3 (mod 4)
      replace h : 4 ∣ b - 3:= by exact (Nat.modEq_iff_dvd' hb).mp (id (Nat.ModEq.symm h))
      zify at h
      field_simp at h
      replace h : 3 ≡ b [ZMOD 4]:= by exact Int.modEq_iff_dvd.mpr h
      replace h : b ≡ -1 [ZMOD 4]:= by exact id (Int.ModEq.symm h)
      -- Show that b^(a_{n+1}) ≥ 3
      replace hb : b ^ (a (n + 1)) ≥ 3 ^ (a (n + 1)):= by exact Nat.pow_le_pow_of_le_left hb (a (n + 1))
      have g : a (n + 1) ≥ 1:= by
        have g : a (n + 1) ≥ a (n + 1) % 4:= by exact Nat.mod_le (a (n + 1)) 4
        rw [ih] at g
        simp at g
        linarith
      replace g : 3 ^ a (n + 1) ≥ 3 ^ 1:= by refine Nat.pow_le_pow_of_le_right (by omega) g
      simp at g
      replace hb : b ^ (a (n + 1)) ≥ 3:= by linarith
      clear g
      -- Prove that 4 divides b^(a_{n+1}) - 3
      suffices 4 ∣ b ^ (a (n + 1)) - 3 by exact Nat.ModEq.symm ((fun {n a b} h => (Nat.modEq_iff_dvd' h).mpr) hb this)
      zify
      field_simp
      suffices b ^ (a (n + 1)) ≡ 3 [ZMOD 4] by exact Int.dvd_sub_of_emod_eq this
      -- Use the fact that b ≡ -1 (mod 4) and a_{n+1} is odd
      replace h : b ^ (a (n + 1)) ≡ (-1) ^ (a (n + 1)) [ZMOD 4]:= by exact Int.ModEq.pow (a (n + 1)) h
      rw [show (-1) ^ a (n + 1) = -1 by exact Odd.neg_one_pow hOdd] at h
      exact h
  -- Main proof: for n ≥ 3, show a_n ≡ b^(b^3 mod 20) (mod 100)
  intro n hn
  set m:= n - 3 with hm
  clear_value m
  replace hm : n = m + 3:= by omega
  subst n
  rw [ha (m + 1), ha m]
  specialize h1 m
  -- Show that a_{m+1} ≥ 3
  have g : a (m + 1) ≥ a (m + 1) % 4:= by exact Nat.mod_le (a (m + 1)) 4
  rw [h1] at g
  simp at g
  -- Express a_{m+1} as 4k + 3 for some k
  replace h1 : 4 ∣ a (m + 1) - 3:= by exact (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm h1))
  rcases h1 with ⟨k, hk⟩
  replace hk : a (m + 1) = 4 * k + 3:= by omega
  rw [hk]
  -- Rewrite b^(4k + 3) as b^(4k) * b^3
  rw [show b ^ (4 * k + 3) = b ^ (4 * k) * b ^ 3 by ring_nf]
  -- Prove that b^(4k) * b^3 ≡ b^3 mod 20 (mod 20)
  have h1 : b ^ (4 * k) * b ^ 3 ≡ b ^ 3 % 20 [MOD 20]:= by
    have h1 : b ^ 3 % 20 ≡ b ^ 3 [MOD 20]:= by exact Nat.mod_modEq (b ^ 3) 20
    suffices b ^ (4 * k) * b ^ 3 ≡ b ^ 3 [MOD 20] by exact Nat.ModEq.trans this (id (Nat.ModEq.symm h1))
    suffices b ^ (4 * k) * b ^ 3 ≡ 1 * b ^ 3 [MOD 20] by simp at this ; exact this
    -- Use Chinese Remainder Theorem: prove congruence modulo 4 and 5 separately
    have h2 : b ^ (4 * k) * b ^ 3 ≡ 1 * b ^ 3 [MOD 4]:= by
      suffices b ^ (4 * k) ≡ 1 [MOD 4] by exact Nat.ModEq.mul this rfl
      replace h : b ^ (4 * k) ≡ 3 ^ (4 * k) [MOD 4]:= by exact Nat.ModEq.pow (4 * k) h
      rw [show 3 ^ (4 * k) = (3 ^ 4) ^ k by exact Nat.pow_mul 3 4 k] at h
      simp at h
      have h2 : 81 ≡ 1 [MOD 4]:= by rfl
      replace h2:= Nat.ModEq.pow k h2
      simp at h2
      exact Nat.ModEq.trans h h2
    have h3 : b ^ (4 * k) * b ^ 3 ≡ 1 * b ^ 3 [MOD 5]:= by
      -- Case analysis on b mod 5
      mod_cases b % 5
      .
        -- Case b ≡ 0 (mod 5)
        simp
        have h3:= Nat.ModEq.pow (4 * k) H
        have h4:= Nat.ModEq.pow 3 H
        simp at h4
        by_cases hk1 : k = 0
        .
          -- If k = 0, then b^(4k) = 1
          rw [hk1]
          simp
          rfl
        .
          -- If k > 0, then b^(4k) = 0 since b ≡ 0 (mod 5)
          rw [show 0 ^ (4 * k) = 0 by refine Nat.zero_pow_of_pos (4 * k) (by omega)] at h3
          replace h3:= Nat.ModEq.mul h3 h4
          simp at h3
          exact Nat.ModEq.trans h3 (id (Nat.ModEq.symm h4))
      all_goals
        -- Cases b ≡ 1,2,3,4 (mod 5): use Fermat's little theorem
        suffices b ^ (4 * k) ≡ 1 [MOD 5] by exact Nat.ModEq.mul this rfl
        replace H:= Nat.ModEq.pow 4 H
        rw [show b ^ (4 * k) = (b ^ 4) ^ k by exact Nat.pow_mul b 4 k]
        rw [show 1 = 1 ^ k by simp]
        suffices b ^ 4 ≡ 1 [MOD 5] by exact Nat.ModEq.pow k H
        simp at H
        exact H
    -- Apply Chinese Remainder Theorem since 4 and 5 are coprime
    rw [show 20 = 4 * 5 by simp]
    have g1 : Nat.Coprime 4 5:= by norm_num
    refine (Nat.modEq_and_modEq_iff_modEq_mul g1).mp ⟨h2, h3⟩
  -- Show that b^(4k) * b^3 ≥ b^3 mod 20
  have h2 : b ^ (4 * k) * b ^ 3 ≥ b ^ 3 % 20:= by
    have g1 : b ^ (4 * k) * b ^ 3 ≥ (b ^ (4 * k) * b ^ 3) % 20:= by exact Nat.mod_le (b ^ (4 * k) * b ^ 3) 20
    rw [h1] at g1
    simp at g1
    exact g1
  -- Prove that b^3 mod 20 > 0
  have h3 : b ^ 3 % 20 > 0:= by
    by_contra H
    simp at H
    replace H : 20 ∣ b ^ 3:= by exact Nat.dvd_of_mod_eq_zero H
    replace H : 2 ∣ b ^ 3:= by omega
    have g1 : Nat.Prime 2:= by norm_num
    replace H : 2 ∣ b:= by exact Nat.Prime.dvd_of_dvd_pow g1 H
    have g2 : b ≥ b % 4:= by exact Nat.mod_le b 4
    rw [h] at g2
    simp at g2
    replace h : 4 ∣ b - 3:= by exact (Nat.modEq_iff_dvd' hb).mp (id (Nat.ModEq.symm h))
    replace h : 2 ∣ b - 3:= by omega
    rw [show b = b - 3 + 3 by omega] at H
    replace H : 2 ∣ 3:= by omega
    omega
  -- Set up variables for the final congruence proof
  set x:= b ^ (4 * k) * b ^ 3
  set y:= b ^ 3 % 20 with hy
  clear_value x y
  -- Prove that b^x ≡ b^y (mod 4)
  have h4 : b ^ x ≡ b ^ y [MOD 4]:= by
    have g1:= Nat.ModEq.pow x h
    have g2:= Nat.ModEq.pow y h
    suffices 3 ^ x ≡ b ^ y [MOD 4] by exact Nat.ModEq.trans g1 this
    suffices 3 ^ x ≡ 3 ^ y [MOD 4] by exact Nat.ModEq.trans this (id (Nat.ModEq.symm g2))
    -- Since 20 divides x - y, we have 2 divides x - y
    replace h1 : 20 ∣ x - y:= by exact (Nat.modEq_iff_dvd' h2).mp (id (Nat.ModEq.symm h1))
    replace h1 : 2 ∣ x - y:= by omega
    rcases h1 with ⟨z, hz⟩
    replace hz : x = 2 * z + y:= by omega
    rw [hz]
    rw [show 3 ^ y = 1 * 3 ^ y by simp]
    rw [show 3 ^ (2 * z + y) = 3 ^ (2 * z) * 3 ^ y by ring_nf]
    rw [show 3 ^ (2 * z) = (3 ^ 2) ^ z by exact Nat.pow_mul 3 2 z]
    rw [show 3 ^ 2 = 9 by rfl]
    rw [show 1 = 1 ^ z by simp]
    suffices 9 ^ z ≡ 1 ^ z [MOD 4] by exact Nat.ModEq.mul this rfl
    suffices 9 ≡ 1 [MOD 4] by exact Nat.ModEq.pow z this
    rfl
  -- Prove that b^x ≡ b^y (mod 25)
  have h5 : b ^ x ≡ b ^ y [MOD 25]:= by
    by_cases h5 : Nat.Coprime b 25
    .
      -- Case 1: b and 25 are coprime, use Euler's theorem
      have h6:= Nat.ModEq.pow_totient h5
      have g1 : Nat.totient 25 = 20:= by
        rw [show 25 = 5 ^ (1 + 1) by simp]
        have g2 : Nat.Prime 5:= by norm_num
        rw [Nat.totient_prime_pow_succ g2 1]
        simp
      rw [g1] at h6
      -- Since 20 divides x - y, we can use the periodicity
      replace h1 : 20 ∣ x - y:= by exact (Nat.modEq_iff_dvd' h2).mp (id (Nat.ModEq.symm h1))
      rcases h1 with ⟨z, hz⟩
      replace hz : x = 20 * z + y:= by omega
      rw [hz]
      rw [show b ^ y = 1 ^ z * b ^ y by simp]
      rw [show b ^ (20 * z + y) = b ^ (20 * z) * b ^ y by ring_nf]
      rw [show b ^ (20 * z) = (b ^ 20) ^ z by exact Nat.pow_mul b 20 z]
      suffices (b ^ 20) ^ z ≡ 1 ^ z [MOD 25] by exact Nat.ModEq.mul this rfl
      suffices b ^ 20 ≡ 1 [MOD 25] by exact Nat.ModEq.pow z this
      exact h6
    .
      -- Case 2: b and 25 are not coprime, so 5 divides b
      have g1 : Nat.Prime 5:= by norm_num
      by_cases hy1 : y = 1
      .
        -- Subcase: y = 1, which leads to a contradiction
        rw [hy] at hy1
        rw [show 1 = 1 % 20 by simp] at hy1
        replace hb : b ^ 3 > 0:= by positivity
        replace hb : b ^ 3 ≥ 1:= by linarith
        replace hy1 : 20 ∣ b ^ 3 - 1:= by exact (Nat.modEq_iff_dvd' hb).mp (id (Eq.symm hy1))
        replace hy1 : 5 ∣ b ^ 3 - 1:= by omega
        have g2 : Nat.Coprime 5 b:= by
          by_contra H
          replace H : 5 ∣ b:= by exact (Nat.Prime.dvd_iff_not_coprime g1).mpr H
          replace H : 5 ∣ b ^ 3:= by refine Dvd.dvd.pow H (by omega)
          rw [show b ^ 3 = b ^ 3 - 1 + 1 by omega] at H
          replace H : 5 ∣ 1:= by omega
          omega
        replace g2 : Nat.Coprime (5 ^ 2) b:= by exact Nat.Coprime.pow_left 2 g2
        simp at g2
        absurd h5
        exact Nat.coprime_comm.mp g2
      .
        -- Subcase: y > 1, so 5 divides b
        replace h5 : 5 ∣ b:= by
          by_contra H
          replace H : Nat.Coprime 5 b:= by exact (Nat.Prime.coprime_iff_not_dvd g1).mpr H
          replace H : Nat.Coprime (5 ^ 2) b:= by exact Nat.Coprime.pow_left 2 H
          simp at H
          absurd h5
          exact Nat.coprime_comm.mp H
        -- Since 5 divides b, 25 divides b^2
        replace h5 : 5 * 5 ∣ b * b:= by exact Nat.mul_dvd_mul h5 h5
        ring_nf at h5
        -- Prove that b^n ≡ 0 (mod 25) for n ≥ 2
        have h6 : ∀ n : ℕ, n ≥ 2 → b ^ n ≡ 0 [MOD 25]:= by
          intro n hn
          set n1:= n - 2 with hn1
          clear_value n1
          replace hn1 : n = n1 + 2:= by omega
          rw [hn1]
          ring_nf
          replace h5 : b ^ 2 ≡ 0 [MOD 25]:= by exact Nat.modEq_zero_iff_dvd.mpr h5
          replace h5 : b ^ 2 * b ^ n1 ≡ 0 * b ^ n1 [MOD 25]:= by exact Nat.ModEq.mul h5 rfl
          simp at h5
          exact h5
        -- Since both x and y are ≥ 2, both b^x and b^y are ≡ 0 (mod 25)
        have h7:= h6 y (by omega)
        replace h6:= h6 x (by omega)
        exact Nat.ModEq.trans h6 (id (Nat.ModEq.symm h7))
  -- Apply Chinese Remainder Theorem to combine the congruences modulo 4 and 25
  rw [show 100 = 4 * 25 by simp]
  refine (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num)).mp ⟨h4, h5⟩
