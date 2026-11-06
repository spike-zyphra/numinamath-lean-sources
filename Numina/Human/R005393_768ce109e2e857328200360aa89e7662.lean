import Mathlib

/- У скупу ненегативних целих бројева решити једначину

$$
\left(2^{2015}+1\right)^{x}+2^{2015}=2^{y}+1 . \quad \text { (Бојан Баиић) }
$$

## РЕШЕЊА -/
theorem number_theory_608101 : {(x, y) : ℕ × ℕ | (2 ^ 2015 + 1) ^ x + 2 ^ 2015 = 2 ^ y + 1} = {(0, 2015), (1, 2016)}:= by
    -- Rewrite 2016 as 2015 + 1 for cleaner calculations
    rw [show 2016 = 2015 + 1 by omega]
    -- Define m as 2015 for easier reference
    set m:= 2015 with hm
    clear_value m
    -- Use extensionality to prove equality of sets
    ext ⟨x, y⟩
    constructor
    .
        -- Forward direction: if (x,y) satisfies the equation, then (x,y) is in {(0,2015), (1,2016)}
        intro h
        simp at h
        -- Case analysis: either x = 0 or x = 1, or x > 1
        by_cases hx : x = 0 ∨ x = 1
        .
            -- Handle the cases x = 0 and x = 1
            rcases hx with hx | hx
            .
                -- Case x = 0
                subst x
                simp at h
                -- Simplify the equation to 2^y = 2^m
                replace h : 2 ^ y = 2 ^ m:= by linarith
                -- Apply logarithm to both sides
                replace h : Nat.log 2 (2 ^ y) = Nat.log 2 (2 ^ m):= by rw [h]
                -- Simplify using the property of logarithms
                rw [show Nat.log 2 (2 ^ y) = y by refine Nat.log_pow (by omega) y] at h
                rw [show Nat.log 2 (2 ^ m) = m by refine Nat.log_pow (by omega) m] at h
                -- Conclude y = m = 2015
                subst y m
                simp
            .
                -- Case x = 1
                subst x
                simp at h
                ring_nf at h
                -- Rewrite 2^m * 2 as 2^(m+1)
                rw [show 2 ^ m * 2 = 2 ^ (m + 1) by ring] at h
                -- Simplify the equation to 2^(m+1) = 2^y
                replace h : 2 ^ (m + 1) = 2 ^ y:= by linarith
                -- Apply logarithm to both sides
                replace h : Nat.log 2 (2 ^ (m + 1)) = Nat.log 2 (2 ^ y):= by rw [h]
                -- Simplify using the property of logarithms
                rw [show Nat.log 2 (2 ^ (m + 1)) = m + 1 by refine Nat.log_pow (by omega) (m + 1)] at h
                rw [show Nat.log 2 (2 ^ y) = y by refine Nat.log_pow (by omega) y] at h
                -- Conclude y = m + 1 = 2016
                rw [←h, hm]
                simp
        .
            -- Case x > 1: prove this case has no solutions using modular arithmetic
            replace hx : x > 1:= by omega
            zify at h
            -- Lemma: if 2^n ≡ 4 (mod 9), then n = 6k + 2 for some k
            have h1 : ∀ n : ℕ, 2 ^ n ≡ 4 [ZMOD 9] → ∃ k : ℕ, n = 6 * k + 2:= by
                intro n hn
                by_cases hn1 : n = 0 ∨ n = 1
                .
                    rcases hn1 with hn1 | hn1
                    all_goals
                        subst n
                        simp [Int.ModEq] at hn
                .
                    replace hn1 : n ≥ 2:= by omega
                    replace hn : (9 : ℤ) ∣ 2 ^ n - 4:= by exact Int.dvd_sub_of_emod_eq hn
                    rw [show n = n - 2 + 2 by omega] at hn
                    rw [show (2 : ℤ) ^ (n - 2 + 2) = 2 ^ (n - 2) * 4 by ring] at hn
                    rw [show (2 : ℤ) ^ (n - 2) * 4 - 4 = 4 * (2 ^ (n - 2) - 1) by ring] at hn
                    replace hn : (9 : ℤ) ∣ 2 ^ (n - 2) - 1:= by exact Int.dvd_of_dvd_mul_right_of_gcd_one hn rfl
                    set N:= n - 2 with hN
                    clear_value N
                    replace hn : 2 ^ N ≡ 1 [ZMOD 9]:= by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) hn)
                    by_cases hNpos : N = 0
                    .
                        subst N
                        use 0
                        simp
                        omega
                    .
                        -- Analyze the case N > 5 using modular arithmetic
                        replace hNpos : N > 5:= by
                            by_contra H
                            replace H : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5:= by omega
                            rcases H with H | H | H | H | H
                            all_goals
                                rw [H] at hn
                                simp [Int.ModEq] at hn
                        -- Case analysis on N modulo 6
                        mod_cases N % 6
                        all_goals
                            replace H:= (Nat.modEq_iff_dvd' (by linarith)).mp (id (Nat.ModEq.symm H))
                            simp [Dvd.dvd] at H
                            rcases H with ⟨k, hk⟩
                            have g1 : 64 ≡ 1 [ZMOD 9]:= by rfl
                            replace g1 : 64 ^ k ≡ 1 ^ k [ZMOD 9]:= by exact Int.ModEq.pow k g1
                            simp at g1
                            rw [show (64 : ℤ) = 2 ^ 6 by norm_num] at g1
                            rw [show ((2 : ℤ) ^ 6) ^ k = 2 ^ (6 * k) by exact Eq.symm (pow_mul 2 6 k)] at g1
                            ring_nf at g1
                        .
                            rw [hN] at hk
                            use k
                            omega
                        .
                            replace hk : N = 6 * k + 1:= by omega
                            rw [hk] at hn
                            ring_nf at hn
                            replace g1 : 2 ^ (k * 6) * 2 ≡ 1 * 2 [ZMOD 9]:= by exact Int.ModEq.mul g1 rfl
                            simp at g1
                            replace g1 : 1 ≡ 2 [ZMOD 9]:= by exact Int.ModEq.trans (id (Int.ModEq.symm hn)) g1
                            simp [Int.ModEq] at g1
                        .
                            replace hk : N = 6 * k + 2:= by omega
                            rw [hk] at hn
                            ring_nf at hn
                            replace g1 : 2 ^ (k * 6) * 4 ≡ 1 * 4 [ZMOD 9]:= by exact Int.ModEq.mul g1 rfl
                            simp at g1
                            replace g1 : 1 ≡ 4 [ZMOD 9]:= by exact Int.ModEq.trans (id (Int.ModEq.symm hn)) g1
                            simp [Int.ModEq] at g1
                        .
                            replace hk : N = 6 * k + 3:= by omega
                            rw [hk] at hn
                            ring_nf at hn
                            replace g1 : 2 ^ (k * 6) * 8 ≡ 1 * 8 [ZMOD 9]:= by exact Int.ModEq.mul g1 rfl
                            simp at g1
                            replace g1 : 1 ≡ 8 [ZMOD 9]:= by exact Int.ModEq.trans (id (Int.ModEq.symm hn)) g1
                            simp [Int.ModEq] at g1
                        .
                            replace hk : N = 6 * k + 4:= by omega
                            rw [hk] at hn
                            ring_nf at hn
                            replace g1 : 2 ^ (k * 6) * 16 ≡ 1 * 16 [ZMOD 9]:= by exact Int.ModEq.mul g1 rfl
                            simp at g1
                            replace g1 : 1 ≡ 16 [ZMOD 9]:= by exact Int.ModEq.trans (id (Int.ModEq.symm hn)) g1
                            simp [Int.ModEq] at g1
                        .
                            replace hk : N = 6 * k + 5:= by omega
                            rw [hk] at hn
                            ring_nf at hn
                            replace g1 : 2 ^ (k * 6) * 32 ≡ 1 * 32 [ZMOD 9]:= by exact Int.ModEq.mul g1 rfl
                            simp at g1
                            replace g1 : 1 ≡ 32 [ZMOD 9]:= by exact Int.ModEq.trans (id (Int.ModEq.symm hn)) g1
                            simp [Int.ModEq] at g1
            -- Prove that 2^m ≡ -1 (mod 3)
            have h2 : 2 ≡ -1 [ZMOD 3]:= by rfl
            replace h2:= Int.ModEq.pow m h2
            rw [show (-1 : ℤ) ^ m = -1 by exact Odd.neg_one_pow (by rw [hm] ; decide)] at h2
            -- Show that 2^m + 1 ≡ 0 (mod 3)
            replace h2 : 2 ^ m + 1 ≡ -1 + 1 [ZMOD 3]:= by exact Int.ModEq.add h2 rfl
            rw [show -1 + 1 = 0 by ring] at h2
            -- Therefore 3 divides 2^m + 1
            replace h2 : (3 : ℤ) ∣ 2 ^ m + 1:= by exact Int.dvd_of_emod_eq_zero h2
            -- Square both sides to show 9 divides (2^m + 1)^2
            replace h2:= Int.mul_dvd_mul h2 h2
            rw [show (3 : ℤ) * 3 = 9 by ring] at h2
            rw [show ((2 : ℤ) ^ m + 1) * (2 ^ m + 1) = (2 ^ m + 1) ^ 2 by ring] at h2
            -- Show that 9 divides (2^m + 1)^x
            replace h2 : (9 : ℤ) ∣ (2 ^ m + 1) ^ 2 * (2 ^ m + 1) ^ (x - 2):= by exact Dvd.dvd.mul_right h2 ((2 ^ m + 1) ^ (x - 2))
            rw [show ((2 : ℤ) ^ m + 1) ^ 2 * (2 ^ m + 1) ^ (x - 2) = (2 ^ m + 1) ^ (2 + (x - 2)) by ring] at h2
            rw [show 2 + (x - 2) = x by omega] at h2
            -- Therefore (2^m + 1)^x ≡ 0 (mod 9)
            replace h2 : (2 ^ m + 1) ^ x ≡ 0 [ZMOD 9]:= by exact Dvd.dvd.modEq_zero_int h2
            -- Show that m = 6k + 5 for some k
            have h3 : ∃ k : ℕ, m = 6 * k + 5:= by use 335
            rcases h3 with ⟨k, hk⟩
            -- Prove that 2^m ≡ 32 (mod 9)
            have h3 : 2 ^ m ≡ 2 ^ 5 [ZMOD 9]:= by
                rw [hk]
                rw [show (2 : ℤ) ^ (6 * k + 5) = 2 ^ (6 * k) * 2 ^ 5 by ring]
                rw [pow_mul 2 6 k]
                ring_nf
                have g1 : 64 ≡ 1 [ZMOD 9]:= by rfl
                replace g1 : 64 ^ k ≡ 1 ^ k [ZMOD 9]:= by exact Int.ModEq.pow k g1
                simp at g1
                replace g1 : 64 ^ k * 32 ≡ 1 * 32 [ZMOD 9]:= by exact Int.ModEq.mul g1 rfl
                simp at g1
                exact g1
            clear hk k
            -- From the original equation and previous results, show 2^y ≡ 32 (mod 9)
            replace h2 : (2 ^ m + 1) ^ x + 2 ^ m ≡ 0 + 32 [ZMOD 9]:= by exact Int.ModEq.add h2 h3
            rw [h] at h2
            simp at h2
            replace h2 : 2 ^ y + 1 - 1 ≡ 32 - 1 [ZMOD 9]:= by exact Int.ModEq.sub h2 rfl
            ring_nf at h2
            -- Apply the lemma to show y = 6k + 2
            specialize h1 y h2
            rcases h1 with ⟨k, hk⟩
            clear h2 h3
            -- Further modular analysis using mod 13
            have h1 : 2 ^ y ≡ (-1) ^ k * 4 [ZMOD 13]:= by
                subst y
                rw [show (2 : ℤ) ^ (6 * k + 2) = 2 ^ (6 * k) * 4 by ring]
                rw [pow_mul 2 6 k]
                ring_nf
                have g1 : 64 ≡ -1 [ZMOD 13]:= by rfl
                replace g1 : 64 ^ k ≡ (-1) ^ k [ZMOD 13]:= by exact Int.ModEq.pow k g1
                exact Int.ModEq.mul g1 rfl
            -- Show that 2^m ≡ 7 (mod 13)
            have h2 : 2 ^ m ≡ 7 [ZMOD 13]:= by
                have h2 : ∃ k : ℕ, m = 12 * k + 11:= by use 167
                rcases h2 with ⟨k, hk⟩
                rw [hk]
                rw [show (2 : ℤ) ^ (12 * k + 11) = 2 ^ (12 * k) * 2 ^ 11 by ring]
                rw [pow_mul 2 12 k]
                ring_nf
                have g1 : 4096 ≡ 1 [ZMOD 13]:= by rfl
                replace g1 : 4096 ^ k ≡ 1 ^ k [ZMOD 13]:= by exact Int.ModEq.pow k g1
                simp at g1
                exact Int.ModEq.mul g1 rfl
            -- Show that 2^m + 1 ≡ 8 (mod 13)
            have h3 : 2 ^ m + 1 ≡ 7 + 1 [ZMOD 13]:= by exact Int.ModEq.add h2 rfl
            rw [show (7 : ℤ) + 1 = 8 by ring] at h3
            -- Therefore (2^m + 1)^x ≡ 8^x (mod 13)
            replace h3 : (2 ^ m + 1) ^ x ≡ 8 ^ x [ZMOD 13]:= by exact Int.ModEq.pow x h3
            -- Combine with the original equation
            replace h3:= Int.ModEq.add h3 h2
            rw [h] at h3
            -- Derive a contradiction using modular arithmetic
            replace h1 : 2 ^ y + 1 ≡ (-1) ^ k * 4 + 1 [ZMOD 13]:= by exact Int.ModEq.add h1 rfl
            replace h1 : 8 ^ x + 7 ≡ (-1) ^ k * 4 + 1 [ZMOD 13]:= by exact Int.ModEq.trans (id (Int.ModEq.symm h3)) h1
            replace h1 : 8 ^ x + 7 - 7 ≡ (-1) ^ k * 4 + 1 - 7 [ZMOD 13]:= by exact Int.ModEq.sub h1 rfl
            ring_nf at h1
            -- Show that 8^x ≡ 3 or 8^x ≡ 11 (mod 13)
            replace h1 : 8 ^ x ≡ 3 [ZMOD 13] ∨ 8 ^ x ≡ 11 [ZMOD 13]:= by
                by_cases hk1 : Odd k
                .
                    rw [show (-1) ^ k = -1 by exact Odd.neg_one_pow hk1] at h1
                    ring_nf at h1
                    left
                    exact h1
                .
                    simp at hk1
                    rw [show (-1) ^ k = 1 by exact Even.neg_one_pow hk1] at h1
                    ring_nf at h1
                    right
                    exact h1
            clear h2 h3 hk h hm k
            -- Establish that x ≥ 3
            replace hx : x ≥ 3:= by
                by_contra H
                replace H : x = 2:= by omega
                subst x
                simp [Int.ModEq] at h1
            -- Case analysis on x modulo 4
            mod_cases x % 4
            all_goals
                replace H:= (Nat.modEq_iff_dvd' (by linarith)).mp (id (Nat.ModEq.symm H))
                simp [Dvd.dvd] at H
                rcases H with ⟨k, hk⟩
                have g1 : 8 ^ 4 ≡ 1 [ZMOD 13]:= by rfl
                replace g1:= Int.ModEq.pow k g1
                rw [Eq.symm (pow_mul 8 4 k)] at g1
                simp at g1
            .
                rw [←hk] at g1
                rcases h1 with h1 | h1
                all_goals
                    apply Int.ModEq.trans (id (Int.ModEq.symm g1)) at h1
                    simp [Int.ModEq] at h1
            .
                replace g1 : 8 ^ (4 * k) * 8 ≡ 1 * 8 [ZMOD 13]:= by exact Int.ModEq.mul g1 rfl
                rw [show (8 : ℤ) ^ (4 * k) * 8 = 8 ^ (4 * k + 1) by ring] at g1
                replace hk : x = 4 * k + 1:= by omega
                rw [←hk] at g1
                rcases h1 with h1 | h1
                all_goals
                    apply Int.ModEq.trans (id (Int.ModEq.symm g1)) at h1
                    simp [Int.ModEq] at h1
            .
                replace g1 : 8 ^ (4 * k) * 8 ^ 2 ≡ 1 * 8 ^ 2 [ZMOD 13]:= by exact Int.ModEq.mul g1 rfl
                rw [show (8 : ℤ) ^ (4 * k) * 8 ^ 2 = 8 ^ (4 * k + 2) by ring] at g1
                replace hk : x = 4 * k + 2:= by omega
                rw [←hk] at g1
                rcases h1 with h1 | h1
                all_goals
                    apply Int.ModEq.trans (id (Int.ModEq.symm g1)) at h1
                    simp [Int.ModEq] at h1
            .
                replace g1 : 8 ^ (4 * k) * 8 ^ 3 ≡ 1 * 8 ^ 3 [ZMOD 13]:= by exact Int.ModEq.mul g1 rfl
                rw [show (8 : ℤ) ^ (4 * k) * 8 ^ 3 = 8 ^ (4 * k + 3) by ring] at g1
                replace hk : x = 4 * k + 3:= by omega
                rw [←hk] at g1
                rcases h1 with h1 | h1
                all_goals
                    apply Int.ModEq.trans (id (Int.ModEq.symm g1)) at h1
                    simp [Int.ModEq] at h1
    .
        -- Backward direction: if (x,y) is in {(0,2015), (1,2016)}, then it satisfies the equation
        intro h
        simp at h
        rcases h with h | h
        .
            -- Case (x,y) = (0,2015)
            rcases h with ⟨h1, h2⟩
            subst x y
            simp
            linarith
        .
            -- Case (x,y) = (1,2016)
            rcases h with ⟨h1, h2⟩
            clear hm
            subst x y
            simp
            ring_nf
