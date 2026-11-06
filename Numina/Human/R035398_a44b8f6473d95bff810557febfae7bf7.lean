import Mathlib
/- Find the smallest positive integer $k$ which is representable in the form $k=19^{n}-5^{m}$ for some positive integers $m$ and $n$. -/
theorem number_theory_241034 : IsLeast {k : ℤ | 0 < k ∧ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ k = 19 ^ n - 5 ^ m} 14:= by
    constructor
    -- First part: Prove that 14 belongs to the set (i.e., 14 can be written as 19^n - 5^m)
    .
        simp
        use 1
        simp
        use 1
        simp
    -- Second part: Prove that 14 is the smallest element in the set
    .
        simp [lowerBounds]
        intro k hk m hm n hn h
        -- Prove that 5^(m+1) ≡ 5 (mod 10) for any natural number m
        have g2 : ∀ m : ℕ, 5 ^ (m + 1) ≡ 5 [ZMOD 10]:= by
            intro m
            induction m with
            | zero => simp
            | succ m ih =>
                rw [show (5 : ℤ) ^ (m + 1 + 1) = 5 ^ (m + 1) * 5 by ring]
                replace ih : 5 ^ (m + 1) * 5 ≡ 5 * 5 [ZMOD 10]:= by exact Int.ModEq.mul ih rfl
                exact ih
        -- Split into two cases based on whether n is even or odd
        by_cases h1 : Even n
        -- Case 1: n is even
        .
            replace h1 : ∃ k : ℕ, n = 2 * k:= by exact Even.exists_two_nsmul n h1
            rcases h1 with ⟨t, ht⟩
            subst n
            -- Rewrite 19^(2*t) as (19^2)^t
            rw [show (19 : ℤ) ^ (2 * t) = (19 ^ 2) ^ t by exact pow_mul 19 2 t] at h
            simp at h
            -- Prove that 361 ≡ 1 (mod 10)
            have g1 : 361 ≡ 1 [ZMOD 10]:= by rfl
            replace g1 : 361 ^ t ≡ 1 ^ t [ZMOD 10]:= by exact Int.ModEq.pow t g1
            simp at g1
            -- Restate the lemma about 5^(m+1) ≡ 5 (mod 10)
            have g2 : ∀ m : ℕ, 5 ^ (m + 1) ≡ 5 [ZMOD 10]:= by
                intro m
                induction m with
                | zero => simp
                | succ m ih =>
                    rw [show (5 : ℤ) ^ (m + 1 + 1) = 5 ^ (m + 1) * 5 by ring]
                    replace ih : 5 ^ (m + 1) * 5 ≡ 5 * 5 [ZMOD 10]:= by exact Int.ModEq.mul ih rfl
                    exact ih
            specialize g2 (m - 1)
            rw [show m - 1 + 1 = m by omega] at g2
            -- Prove that k ≡ 6 (mod 10)
            have h1 : k ≡ 6 [ZMOD 10]:= by
                suffices k ≡ 1 - 5 [ZMOD 10] by exact this
                rw [h]
                exact Int.ModEq.sub g1 g2
            -- Contradiction if k < 14
            by_contra H
            simp at H
            replace h1 : 10 ∣ k - 6:= by exact Int.dvd_sub_of_emod_eq h1
            replace h1 : ∃ a : ℤ, k - 6 = 10 * a:= by exact h1
            rcases h1 with ⟨a, ha⟩
            have ha1 : a = 0:= by omega
            subst a
            simp at ha
            replace ha : k = 6:= by omega
            subst k
            -- Prove that m must be even
            have hmeven : Even m:= by
                by_contra H
                simp at H
                have g1 : 5 ≡ -1 [ZMOD 3]:= by rfl
                have g2 : 5 ^ m ≡ (-1) ^ m [ZMOD 3]:= by exact Int.ModEq.pow m g1
                have g3 : 361 ≡ 1 [ZMOD 3]:= by rfl
                replace g3 : 361 ^ t ≡ 1 ^ t [ZMOD 3]:= by exact Int.ModEq.pow t g3
                simp at g3
                replace g3 : 361 ^ t - 5 ^ m ≡ 1 - (-1) ^ m [ZMOD 3]:= by exact Int.ModEq.sub g3 g2
                rw [ha] at g3
                rw [show (-1 : ℤ) ^ m = -1 by exact Odd.neg_one_pow H] at g3
                simp at g3
                replace g3 : (3 : ℤ) ∣ (6 - 2):= by exact Int.dvd_sub_of_emod_eq g3
                omega
            replace hmeven : ∃ s : ℕ, m = 2 * s:= by exact Even.exists_two_nsmul m hmeven
            rcases hmeven with ⟨s, hs⟩
            subst m
            -- Derive a contradiction using the factorization of 19^(2t) - 5^(2s)
            replace ha : ((19 : ℤ) ^ t + 5 ^ s) * (19 ^ t - 5 ^ s) = 6:= by
                ring_nf
                rw [show s * 2 = 2 * s by ring]
                rw [show t * 2 = 2 * t by ring]
                rw [show (5 : ℤ) ^ (2 * s) = (5 ^ 2) ^ s by exact pow_mul 5 2 s]
                rw [show (19 : ℤ) ^ (2 * t) = (19 ^ 2) ^ t by exact pow_mul 19 2 t]
                ring_nf
                rw [show (5 : ℤ) ^ (2 * s) = (5 ^ 2) ^ s by exact pow_mul 5 2 s] at ha
                ring_nf at ha
                linarith
            -- Prove that 19^t - 5^s > 0
            have g1 : (19 : ℤ) ^ t - 5 ^ s > 0:= by
                by_contra H
                simp at H
                replace H : (5 : ℤ) ^ s - 19 ^ t ≥ 0:= by linarith
                replace H : ((5 : ℤ) ^ s - 19 ^ t) * ((19 : ℤ) ^ t + 5 ^ s) ≥ 0:= by positivity
                linarith
            -- Prove that 19^t + 5^s ≥ 24
            have g2 : (19 : ℤ) ^ t + 5 ^ s ≥ 24:= by
                replace hn : t > 0:= by linarith
                replace hm : s > 0:= by linarith
                replace hn : t ≥ 1:= by omega
                replace hm : s ≥ 1:= by omega
                have g3 : (19 : ℤ) ^ t ≥ 19 ^ 1:= by refine pow_le_pow_right₀ (by linarith) hn
                have g4 : (5 : ℤ) ^ s ≥ 5 ^ 1:= by refine pow_le_pow_right₀ (by linarith) hm
                linarith
            -- Derive final contradiction
            replace g1 : (19 : ℤ) ^ t - 5 ^ s ≥ 1:= by omega
            replace g1 : ((19 : ℤ) ^ t - 5 ^ s) * ((19 : ℤ) ^ t + 5 ^ s) ≥ 1 * 24:= by refine Int.mul_le_mul g1 g2 (by linarith) (by linarith)
            linarith
        -- Case 2: n is odd
        .
            simp at h1
            replace h1 : ∃ k : ℕ, n = 2 * k + 1:= by exact h1
            rcases h1 with ⟨t, ht⟩
            subst n
            ring_nf at h
            rw [show t * 2 = 2 * t by ring] at h
            rw [show (19 : ℤ) ^ (2 * t) = (19 ^ 2) ^ t by exact pow_mul 19 2 t] at h
            simp at h
            -- Prove that 361 ≡ 1 (mod 10)
            have g1 : 361 ≡ 1 [ZMOD 10]:= by rfl
            replace g1 : 361 ^ t ≡ 1 ^ t [ZMOD 10]:= by exact Int.ModEq.pow t g1
            simp at g1
            specialize g2 (m - 1)
            rw [show m - 1 + 1 = m by omega] at g2
            replace g1 : 361 ^ t * 19 ≡ 1 * 19 [ZMOD 10]:= by exact Int.ModEq.mul g1 rfl
            replace h : k = 361 ^ t * 19 - 5 ^ m:= by omega
            simp at g1
            -- Prove that k ≡ 4 (mod 10)
            replace g1 : 361 ^ t * 19 - 5 ^ m ≡ 19 - 5 [ZMOD 10]:= by exact Int.ModEq.sub g1 g2
            rw [←h] at g1
            simp at g1
            replace g1 : k ≡ 4 [ZMOD 10]:= by exact g1
            replace g1 : 10 ∣ k - 4:= by exact Int.dvd_sub_of_emod_eq g1
            replace g1 : ∃ a : ℤ, k - 4 = 10 * a:= by exact g1
            rcases g1 with ⟨a, ha⟩
            -- Contradiction if k < 14
            by_contra H
            simp at H
            have ha1 : a = 0:= by omega
            subst a
            simp at ha
            replace ha : k = 4:= by omega
            subst k
            -- Work with modular arithmetic mod 3
            have g1 : 361 ≡ 1 [ZMOD 3]:= by rfl
            have g2 : 361 ^ t ≡ 1 ^ t [ZMOD 3]:= by exact Int.ModEq.pow t g1
            simp at g2
            replace g2 : 361 ^ t * 19 ≡ 1 * 19 [ZMOD 3]:= by exact Int.ModEq.mul g2 rfl
            simp at g2
            replace ha : (361 : ℤ) ^ t * 19 - 4 = 5 ^ m:= by omega
            replace g2 : 361 ^ t * 19 - 4 ≡ 19 - 4 [ZMOD 3]:= by exact Int.ModEq.sub g2 g1
            rw [ha] at g2
            simp at g2
            -- Derive contradiction using divisibility by 3
            replace g2 : 5 ^ m ≡ 0 [ZMOD 3]:= by exact g2
            replace g2 : (3 : ℤ) ∣ 5 ^ m:= by exact Int.dvd_of_emod_eq_zero g2
            replace g2 : 3 ∣ 5 ^ m:= by zify ; exact g2
            have g3 : Nat.Prime 3:= by norm_num
            replace g2 : 3 ∣ 5:= by exact Nat.Prime.dvd_of_dvd_pow g3 g2
            omega
