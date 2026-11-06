import Mathlib
/- Déterminer tous les entiers naturels $n$ tels que 21 divise $2^{2^{n}}+2^{n}+1$. -/
theorem number_theory_607427 (n : ℕ) : 21 ∣ 2 ^ (2 ^ n) + 2 ^ n + 1 ↔ n ≡ 2 [MOD 6]:= by
    -- We'll prove both directions of the equivalence
    constructor
    -- First direction: if 21 divides 2^(2^n) + 2^n + 1, then n ≡ 2 [MOD 6]
    .
        intro h
        by_cases hn : n = 2
        -- Case: n = 2
        .
            subst n
            rfl
        -- Case: n ≠ 2
        .
            -- First, we prove that n ≥ 5
            replace h1 : n ≥ 5:= by
                by_contra H
                replace H : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 4:= by omega
                rcases H with H | H | H | H
                all_goals
                    subst n
                    simp at h
                    omega
            -- Next, we prove that n is even
            have h2 : Even n:= by
                by_contra H
                simp at H
                zify at h
                rw [show (21 : ℤ) = 3 * 7 by ring] at h
                replace h : (3 : ℤ) ∣ 2 ^ (2 ^ n) + 2 ^ n + 1:= by exact dvd_of_mul_right_dvd h
                rw [show (2 : ℤ) ^ (2 ^ n) + 2 ^ n + 1 = 2 ^ (2 ^ n) + (2 ^ n + 1) by ring] at h
                have g1 : 2 ≡ -1 [ZMOD 3]:= by rfl
                replace g1 : 2 ^ n ≡ (-1) ^ n [ZMOD 3]:= by exact Int.ModEq.pow n g1
                rw [show (-1 : ℤ) ^ n = -1 by exact Odd.neg_one_pow H] at g1
                replace g1 : (3 : ℤ) ∣ 2 ^ n - (-1):= by exact Int.ModEq.dvd (id (Int.ModEq.symm g1))
                simp at g1
                replace h : (3 : ℤ) ∣ 2 ^ (2 ^ n):= by exact (Int.dvd_iff_dvd_of_dvd_add h).mpr g1
                have g2 : Nat.Prime 3:= by norm_num
                replace h : 3 ∣ 2 ^ (2 ^ n):= by zify ; exact h
                replace h : 3 ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow g2 h
                omega
            -- Since n is even, we can write n = 2m
            replace h2 : ∃ m : ℕ, n = m + m:= by exact h2
            rcases h2 with ⟨m, hm⟩
            rw [show m + m = 2 * m by ring] at hm
            subst n
            -- Now we prove that m ≡ 1 [MOD 3]
            have h2 : m ≡ 1 [MOD 3]:= by
                rw [show 2 ^ (2 * m) = (2 ^ 2) ^ m by exact Nat.pow_mul 2 2 m] at h
                rw [show 2 ^ 2 = 4 by norm_num] at h
                rw [show 21 = 3 * 7 by ring] at h
                replace h : 7 ∣ 2 ^ (4 ^ m) + 4 ^ m + 1:= by exact dvd_of_mul_left_dvd h
                have h2 : 4 ≡ 1 [MOD 3]:= by rfl
                replace h2 : 4 ^ m ≡ 1 ^ m [MOD 3]:= by exact Nat.ModEq.pow m h2
                simp at h2
                have h3 : 4 ^ m > 0:= by positivity
                replace h2 : 3 ∣ 4 ^ m - 1:= by exact (Nat.modEq_iff_dvd' h3).mp (id (Nat.ModEq.symm h2))
                replace h2 : ∃ a : ℕ, 4 ^ m - 1 = 3 * a:= by exact h2
                rcases h2 with ⟨a, ha⟩
                replace ha : 4 ^ m = 3 * a + 1:= by omega
                clear h3
                replace ha : 2 ^ (4 ^ m) = 2 ^ (3 * a + 1):= by rw [ha]
                rw [show 2 ^ (3 * a + 1) = 2 ^ (3 * a) * 2 by ring] at ha
                rw [show 2 ^ (3 * a) = (2 ^ 3) ^ a by exact pow_mul 2 3 a] at ha
                rw [show 2 ^ 3 = 8 by norm_num] at ha
                have g1 : 8 ≡ 1 [MOD 7]:= by rfl
                replace g1 : 8 ^ a ≡ 1 ^ a [MOD 7]:= by exact Nat.ModEq.pow a g1
                simp at g1
                replace g1 : 8 ^ a * 2 ≡ 1 * 2 [MOD 7]:= by exact Nat.ModEq.mul g1 rfl
                simp at g1
                rw [←ha] at g1
                replace h : 2 ^ (4 ^ m) + 4 ^ m + 1 ≡ 0 [MOD 7]:= by exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat h)
                replace g1 : 2 ^ (4 ^ m) + (4 ^ m + 1) ≡ 2 + (4 ^ m + 1) [MOD 7]:= by exact Nat.ModEq.add g1 rfl
                rw [show 2 ^ 4 ^ m + (4 ^ m + 1) = 2 ^ 4 ^ m + 4 ^ m + 1 by ring] at g1
                rw [show 2 + (4 ^ m + 1) = 4 ^ m + 3 by ring] at g1
                replace h : 4 ^ m + 3 ≡ 0 [MOD 7]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h)) g1)
                -- Case analysis on m modulo 3
                mod_cases m % 3
                -- Case: m ≡ 0 [MOD 3]
                .
                    replace H:= (Nat.modEq_iff_dvd' (by linarith)).mp (id (Nat.ModEq.symm H))
                    simp [Dvd.dvd] at H
                    rcases H with ⟨k, hk⟩
                    subst m
                    rw [show 4 ^ (3 * k) = (4 ^ 3) ^ k by exact pow_mul 4 3 k] at h
                    ring_nf at h
                    have g2 : 64 ≡ 1 [MOD 7]:= by rfl
                    replace g2 : 64 ^ k ≡ 1 ^ k [MOD 7]:= by exact Nat.ModEq.pow k g2
                    simp at g2
                    replace g2 : 3 + 64 ^ k ≡ 3 + 1 [MOD 7]:= by exact Nat.ModEq.add_left 3 g2
                    simp at g2
                    replace h : 4 ≡ 0 [MOD 7]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h)) g2)
                    simp [Nat.ModEq] at h
                -- Case: m ≡ 1 [MOD 3]
                .
                    exact H
                -- Case: m ≡ 2 [MOD 3]
                .
                    replace H:= (Nat.modEq_iff_dvd' (by linarith)).mp (id (Nat.ModEq.symm H))
                    simp [Dvd.dvd] at H
                    rcases H with ⟨k, hk⟩
                    replace hk : m = 3 * k + 2:= by omega
                    replace hk : 4 ^ m = 4 ^ (3 * k + 2):= by rw [hk]
                    rw [show 4 ^ (3 * k + 2) = 4 ^ (3 * k) * 4 ^ 2 by ring] at hk
                    rw [show 4 ^ (3 * k) = (4 ^ 3) ^ k by exact pow_mul 4 3 k] at hk
                    ring_nf at hk
                    have g2 : 64 ≡ 1 [MOD 7]:= by rfl
                    replace g2 : 64 ^ k ≡ 1 ^ k [MOD 7]:= by exact Nat.ModEq.pow k g2
                    simp at g2
                    replace g2 : 64 ^ k * 16 ≡ 1 * 16 [MOD 7]:= by exact Nat.ModEq.mul g2 rfl
                    simp at g2
                    rw [←hk] at g2
                    replace g2 : 4 ^ m + 3 ≡ 16 + 3 [MOD 7]:= by exact Nat.ModEq.add g2 rfl
                    simp at g2
                    replace h : 19 ≡ 0 [MOD 7]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h)) g2)
                    simp [Nat.ModEq] at h
            -- Since m ≡ 1 [MOD 3], we can write m = 3a + 1
            replace h1 : m ≥ 1:= by omega
            replace h2 : 3 ∣ m - 1:= by exact (Nat.modEq_iff_dvd' h1).mp (id (Nat.ModEq.symm h2))
            replace h2 : ∃ a : ℕ, m - 1 = 3 * a:= by exact h2
            rcases h2 with ⟨a, ha⟩
            replace ha : m = 3 * a + 1:= by omega
            subst m
            ring_nf
            -- Finally, we show that 2 * (3 * a + 1) ≡ 2 [MOD 6]
            have g1 : 6 ≡ 0 [MOD 6]:= by rfl
            replace g1 : a * 6 ≡ a * 0 [MOD 6]:= by exact Nat.ModEq.mul rfl g1
            simp at g1
            replace g1 : 2 + a * 6 ≡ 2 + 0 [MOD 6]:= by exact Nat.ModEq.add_left 2 g1
            simp at g1
            exact g1
    -- Second direction: if n ≡ 2 [MOD 6], then 21 divides 2^(2^n) + 2^n + 1
    .
        intro h
        -- First, we prove that n ≥ 2
        have hn : n ≥ 2:= by
            by_contra H
            replace H : n = 0 ∨ n = 1:= by omega
            rcases H with H | H
            all_goals
                subst n
                simp [Nat.ModEq] at h
        -- We'll show that both 3 and 7 divide our expression
        rw [show 21 = 3 * 7 by ring]
        -- First, we prove that n is even
        have heven : Even n:= by
            replace h : 6 ∣ n - 2:= by exact (Nat.modEq_iff_dvd' hn).mp (id (Nat.ModEq.symm h))
            replace h : ∃ m : ℕ, n - 2 = 6 * m:= by exact h
            rcases h with ⟨m, hm⟩
            replace hm : n = 6 * m + 2:= by omega
            have g1 : Even 2:= by decide
            have g2 : Even 6:= by decide
            replace g2 : Even (6 * m):= by exact Even.mul_right g2 m
            subst n
            exact Even.add g2 g1
        -- Now we prove that 3 divides our expression
        have h1 : 3 ∣ 2 ^ (2 ^ n) + 2 ^ n + 1:= by
            zify
            suffices 2 ^ (2 ^ n) + 2 ^ n + 1 ≡ 0 [ZMOD 3] by exact Int.dvd_of_emod_eq_zero this
            have g1 : 2 ≡ -1 [ZMOD 3]:= by rfl
            have g2 : 2 ^ (2 ^ n) ≡ (-1) ^ (2 ^ n) [ZMOD 3]:= by exact Int.ModEq.pow (2 ^ n) g1
            replace g1 : 2 ^ n ≡ (-1) ^ n [ZMOD 3]:= by exact Int.ModEq.pow n g1
            rw [show (-1 : ℤ) ^ n = 1 by exact Even.neg_one_pow heven] at g1
            have h1 : Even 2:= by decide
            replace h1 : Even (2 ^ n):= by refine (Nat.even_pow' (by omega)).mpr h1
            rw [show (-1) ^ (2 ^ n) = 1 by exact Even.neg_one_pow h1] at g2
            replace g2 : 2 ^ (2 ^ n) + 2 ^ n ≡ 1 + 1 [ZMOD 3]:= by exact Int.ModEq.add g2 g1
            simp at g2
            replace g2 : 2 ^ (2 ^ n) + 2 ^ n + 1 ≡ 2 + 1 [ZMOD 3]:= by exact Int.ModEq.add g2 rfl
            exact g2
        -- Next, we prove that 7 divides our expression
        have h2 : 7 ∣ 2 ^ (2 ^ n) + 2 ^ n + 1:= by
            have g1 : 3 ∣ 6:= by omega
            replace h : n ≡ 2 [MOD 3]:= by exact Nat.ModEq.of_dvd g1 h
            zify
            -- First, we show that 2^(2^n) ≡ 2 [MOD 7]
            have h2 : 2 ^ (2 ^ n) ≡ 2 [ZMOD 7]:= by
                replace heven : ∃ m : ℕ, n = m + m:= by exact heven
                rcases heven with ⟨m, hm⟩
                rw [show m + m = 2 * m by ring] at hm
                subst n
                rw [show 2 ^ (2 * m) = (2 ^ 2) ^ m by exact pow_mul 2 2 m]
                rw [show 2 ^ 2 = 4 by norm_num]
                replace g1 : 4 ≡ 1 [MOD 3]:= by rfl
                replace g1 : 4 ^ m ≡ 1 ^ m [MOD 3]:= by exact Nat.ModEq.pow m g1
                simp at g1
                have g2 : 4 ^ m > 0:= by positivity
                replace g1 : 3 ∣ 4 ^ m - 1:= by exact (Nat.modEq_iff_dvd' g2).mp (id (Nat.ModEq.symm g1))
                replace g1 : ∃ a : ℕ, 4 ^ m - 1 = 3 * a:= by exact g1
                rcases g1 with ⟨a, ha⟩
                replace ha : 4 ^ m = 3 * a + 1:= by omega
                clear g2
                rw [ha]
                rw [show (2 : ℤ) ^ (3 * a + 1) = 2 ^ (3 * a) * 2 by ring]
                rw [show (2 : ℤ) ^ (3 * a) = (2 ^ 3) ^ a by exact pow_mul 2 3 a]
                ring_nf
                have g1 : 8 ≡ 1 [ZMOD 7]:= by rfl
                replace g1 : 8 ^ a ≡ 1 ^ a [ZMOD 7]:= by exact Int.ModEq.pow a g1
                simp at g1
                replace g1 : 8 ^ a * 2 ≡ 1 * 2 [ZMOD 7]:= by exact Int.ModEq.mul g1 rfl
                simp at g1
                exact g1
            -- Since n ≡ 2 [MOD 3], we can write n = 3m + 2
            replace h : 3 ∣ n - 2:= by exact (Nat.modEq_iff_dvd' hn).mp (id (Nat.ModEq.symm h))
            replace h : ∃ m : ℕ, n - 2 = 3 * m:= by exact h
            rcases h with ⟨m, hm⟩
            replace hm : n = 3 * m + 2:= by omega
            -- Now we show that 2^n ≡ 4 [MOD 7]
            have h3 : 2 ^ n ≡ 4 [ZMOD 7]:= by
                subst n
                rw [show (2 : ℤ) ^ (3 * m + 2) = 2 ^ (3 * m) * 4 by ring]
                rw [show (2 : ℤ) ^ (3 * m) = (2 ^ 3) ^ m by exact pow_mul 2 3 m]
                ring_nf
                replace g1 : 8 ≡ 1 [ZMOD 7]:= by rfl
                replace g1 : 8 ^ m ≡ 1 ^ m [ZMOD 7]:= by exact Int.ModEq.pow m g1
                simp at g1
                replace g1 : 8 ^ m * 4 ≡ 1 * 4 [ZMOD 7]:= by exact Int.ModEq.mul g1 rfl
                simp at g1
                exact g1
            -- Combining our results to show that 2^(2^n) + 2^n + 1 ≡ 0 [MOD 7]
            replace h2 : 2 ^ (2 ^ n) + 2 ^ n ≡ 2 + 4 [ZMOD 7]:= by exact Int.ModEq.add h2 h3
            replace h2 : 2 ^ (2 ^ n) + 2 ^ n + 1 ≡ 2 + 4 + 1 [ZMOD 7]:= by exact Int.ModEq.add h2 rfl
            simp at h2
            replace h2 : 2 ^ (2 ^ n) + 2 ^ n + 1 ≡ 0 [ZMOD 7]:= by exact h2
            exact Int.dvd_of_emod_eq_zero h2
        -- Finally, we use the Chinese remainder theorem to conclude
        have h3 : Nat.Coprime 3 7:= by norm_num
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h3 h1 h2
