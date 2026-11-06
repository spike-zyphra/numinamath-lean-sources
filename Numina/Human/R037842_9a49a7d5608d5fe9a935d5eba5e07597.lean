import Mathlib
/- Suppose that $m, n, k$ are positive integers satisfying $$3mk=(m+3)^n+1.$$
Prove that $k$ is odd. -/
theorem number_theory_31249 (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (hne : ¬(4 ∣ m)) (h : 3 * m * k = (m + 3) ^ n + 1) : Odd k:= by
  -- First, we prove that m ≡ 2 (mod 3) and n is odd
  have h1 : m ≡ 2 [MOD 3] ∧ Odd n:= by
    -- Working with the main equation modulo 3
    replace h : 3 * m * k ≡ (m + 3) ^ n + 1 [MOD 3]:= by rw [h]
    -- Left side of equation is divisible by 3
    have g1 : 3 * m * k ≡ 0 [MOD 3]:= by
      suffices 3 ∣ 3 * m * k by exact Nat.modEq_zero_iff_dvd.mpr this
      rw [show 3 * m * k = 3 * (m * k) by ring]
      simp
    -- Therefore (m + 3)^n + 1 ≡ 0 (mod 3)
    replace h : (m + 3) ^ n + 1 ≡ 0 [MOD 3]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm g1)) h)
    -- Since 3 ≡ 0 (mod 3), we have m + 3 ≡ m (mod 3)
    replace g1 : m + 3 ≡ m [MOD 3]:= by simp
    -- Therefore (m + 3)^n ≡ m^n (mod 3)
    replace g1 : (m + 3) ^ n ≡ m ^ n [MOD 3]:= by exact Nat.ModEq.pow n g1
    -- And (m + 3)^n + 1 ≡ m^n + 1 (mod 3)
    replace g1 : (m + 3) ^ n + 1 ≡ m ^ n + 1 [MOD 3]:= by exact Nat.ModEq.add_right 1 g1
    -- So m^n + 1 ≡ 0 (mod 3)
    replace h : m ^ n + 1 ≡ 0 [MOD 3]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h)) g1)
    -- Case analysis on m modulo 3
    mod_cases m % 3
    -- Case: m ≡ 0 (mod 3)
    .
      replace H : m ^ n ≡ 0 ^ n [MOD 3]:= by exact Nat.ModEq.pow n H
      rw [show 0 ^ n = 0 by exact Nat.zero_pow_of_pos n hn] at H
      replace H : m ^ n + 1 ≡ 0 + 1 [MOD 3]:= by exact Nat.ModEq.add_right 1 H
      simp at H
      replace h : 1 ≡ 0 [MOD 3]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h)) H)
      simp [Nat.ModEq] at h
    -- Case: m ≡ 1 (mod 3)
    .
      replace H : m ^ n ≡ 1 ^ n [MOD 3]:= by exact Nat.ModEq.pow n H
      rw [show 1 ^ n = 1 by exact Nat.one_pow n] at H
      replace H : m ^ n + 1 ≡ 1 + 1 [MOD 3]:= by exact Nat.ModEq.add_right 1 H
      simp at H
      replace h : 2 ≡ 0 [MOD 3]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h)) H)
      simp [Nat.ModEq] at h
    -- Case: m ≡ 2 (mod 3)
    .
      -- We now have m ≡ 2 (mod 3), need to prove n is odd
      refine ⟨H, ?_⟩
      -- First, we show m ≥ 2
      have g2 : m ≥ 2:= by
        by_contra H1
        simp at H1
        replace H1 : m = 1:= by omega
        subst m
        simp [Nat.ModEq] at H
      -- Proof by contradiction: assume n is even
      by_contra H1
      simp at H1
      -- Since m ≡ 2 (mod 3), we have 3 | (m - 2)
      replace H : 2 ≡ m [MOD 3]:= by exact id (Nat.ModEq.symm H)
      replace H : 3 ∣ m - 2:= by exact (Nat.modEq_iff_dvd' g2).mp H
      -- This means m ≡ -1 (mod 3) in integers
      replace H : m ≡ -1 [ZMOD 3]:= by
        replace H : ∃ l : ℕ, m - 2 = 3 * l:= by exact H
        rcases H with ⟨l, hl⟩
        replace hl : m = 3 * l + 2:= by omega
        subst m
        simp
        have g1 : 3 ≡ 0 [ZMOD 3]:= by rfl
        replace g1 : 3 * l ≡ 0 * l [ZMOD 3]:= by exact Int.ModEq.mul g1 rfl
        simp at g1
        replace g1 : 3 * l + 2 ≡ 0 + 2 [ZMOD 3]:= by exact Int.ModEq.add g1 rfl
        simp at g1
        exact g1
      -- From our main equation, 3 divides m^n + 1
      replace h : 3 ∣ m ^ n + 1:= by exact Nat.dvd_of_mod_eq_zero h
      zify at h
      replace h : m ^ n + 1 ≡ 0 [ZMOD 3]:= by exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int h)
      -- Since m ≡ -1 (mod 3), m^n ≡ (-1)^n (mod 3)
      replace H : m ^ n ≡ (-1) ^ n [ZMOD 3]:= by exact Int.ModEq.pow n H
      -- Since n is even, (-1)^n = 1
      rw [show (-1 : ℤ) ^ n = 1 by exact Even.neg_one_pow H1] at H
      replace H : m ^ n + 1 ≡ 1 + 1 [ZMOD 3]:= by exact Int.ModEq.add_right 1 H
      simp at H
      -- This leads to 2 ≡ 0 (mod 3), which is a contradiction
      replace H : 2 ≡ 0 [ZMOD 3]:= by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h)) H)
      simp [Int.ModEq] at H

  -- Extract the fact that m ≡ 2 (mod 3)
  rcases h1 with ⟨h1, _⟩
  -- Case analysis on whether m is odd or even
  by_cases h3 : Odd m
  -- Case: m is odd
  .
    -- 3 is odd
    have h4 : Odd 3:= by decide
    -- m + 3 is even (odd + odd = even)
    replace h3 : Even (m + 3):= by exact Odd.add_odd h3 h4
    -- (m + 3)^n is even (any power of an even number is even)
    replace h3 : Even ((m + 3) ^ n):= by refine (Nat.even_pow' (by omega)).mpr h3
    -- (m + 3)^n + 1 is odd (even + 1 = odd)
    replace h3 : Odd ((m + 3) ^ n + 1):= by exact Even.add_one h3
    -- Proof by contradiction: assume k is even
    by_contra H
    simp at H
    -- If k is even, then 3*m*k is even
    replace H : Even (3 * m * k):= by exact Even.mul_left H (3 * m)
    -- But this contradicts that (m + 3)^n + 1 is odd
    absurd h3
    simp
    rw [←h]
    exact H
  -- Case: m is even
  .
    simp at h3
    simp [Even] at h3
    rcases h3 with ⟨r, h3⟩
    rw [show r + r = 2 * r by ring] at h3
    subst m
    -- Substitute m = 2r into the main equation
    rw [show 3 * (2 * r) * k = 6 * r * k by ring] at h
    -- Prove that r must be odd
    have h3 : Odd r:= by
      by_contra H
      simp at H
      simp [Even] at H
      rcases H with ⟨t, ht⟩
      rw [show t + t = 2 * t by ring] at ht
      subst r
      rw [show 2 * (2 * t) = 4 * t by ring] at hne
      simp at hne
    -- Express r as 2l + 1 (odd number)
    simp [Odd] at h3
    rcases h3 with ⟨l, h3⟩
    subst r
    -- Proof by contradiction: assume k is even
    by_contra H
    simp at H
    rcases H with ⟨t, ht⟩
    rw [show t + t = 2 * t by ring] at ht
    subst k
    -- Substitute k = 2t into the main equation
    rw [show 6 * (2 * l + 1) * (2 * t) = 3 * t * (2 * l + 1) * 4 by ring] at h
    -- 4 divides the left side of the equation
    have h3 : 4 ∣ 3 * t * (2 * l + 1) * 4:= by simp
    rw [h] at h3
    -- Simplify (m + 3) = (2*(2*l+1) + 3) = 4*l + 5
    rw [show 2 * (2 * l + 1) + 3 = 4 * l + 5 by ring] at h3
    -- So 4 divides (4*l + 5)^n + 1
    replace h3 : (4 * l + 5) ^ n + 1 ≡ 0 [MOD 4]:= by exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat h3)
    -- 4*l ≡ 0 (mod 4)
    have g1 : 4 ≡ 0 [MOD 4]:= by rfl
    replace g1 : 4 * l ≡ 0 * l [MOD 4]:= by exact Nat.ModEq.mul g1 rfl
    simp at g1
    -- So 4*l + 5 ≡ 5 ≡ 1 (mod 4)
    replace g1 : 4 * l + 5 ≡ 0 + 5 [MOD 4]:= by exact Nat.ModEq.add g1 rfl
    simp at g1
    replace g1 : 4 * l + 5 ≡ 1 [MOD 4]:= by exact g1
    -- Therefore (4*l + 5)^n ≡ 1^n ≡ 1 (mod 4)
    replace g1 : (4 * l + 5) ^ n ≡ 1 ^ n [MOD 4]:= by exact Nat.ModEq.pow n g1
    simp at g1
    -- So (4*l + 5)^n + 1 ≡ 1 + 1 ≡ 2 (mod 4)
    replace g1 : (4 * l + 5) ^ n + 1 ≡ 1 + 1 [MOD 4]:= by exact Nat.ModEq.add_right 1 g1
    simp at g1
    -- This leads to 2 ≡ 0 (mod 4), which is a contradiction
    replace g1 : 2 ≡ 0 [MOD 4]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h3)) g1)
    simp [Nat.ModEq] at g1
