import Mathlib
/- Trouver tous les entiers strictement positifs $n$ tels que $2^{n-1} n+1$ soit un carré parfait. -/
theorem number_theory_607608 (n : ℕ) (hn : n > 0) : (∃ k, k ^ 2 = 2 ^ (n - 1) * n + 1) ↔ n = 5:= by
    -- We'll prove both directions of the equivalence
    constructor
    -- Forward direction: if 2^(n-1) * n + 1 is a perfect square, then n = 5
    .
        intro hk
        rcases hk with ⟨k, hk⟩
        -- First, we prove that n ≥ 5
        have h1 : n ≥ 5:= by
            by_contra H
            simp at H
            replace H : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4:= by omega
            rcases H with H | H | H | H
            -- Case n = 1: Show this leads to a contradiction
            .
                subst n
                simp at hk
                have hk1 : k > 1:= by
                    by_contra H
                    simp at H
                    replace H : k ^ 2 ≤ 1:= by nlinarith only [H]
                    linarith
                have hk2 : k < 2:= by
                    by_contra H
                    simp at H
                    replace H : k ^ 2 ≥ 4:= by nlinarith only [H]
                    linarith
                linarith
            -- Case n = 2: Show this leads to a contradiction
            .
                subst n
                simp at hk
                have hk1 : k > 2:= by
                    by_contra H
                    simp at H
                    replace H : k ^ 2 ≤ 4:= by nlinarith only [H]
                    linarith
                have hk2 : k < 3:= by
                    by_contra H
                    simp at H
                    replace H : k ^ 2 ≥ 9:= by nlinarith only [H]
                    linarith
                linarith
            -- Case n = 3: Show this leads to a contradiction
            .
                subst n
                simp at hk
                have hk1 : k > 3:= by
                    by_contra H
                    simp at H
                    replace H : k ^ 2 ≤ 9:= by nlinarith only [H]
                    linarith
                have hk2 : k < 4:= by
                    by_contra H
                    simp at H
                    replace H : k ^ 2 ≥ 16:= by nlinarith only [H]
                    linarith
                linarith
            -- Case n = 4: Show this leads to a contradiction
            .
                subst n
                simp at hk
                have hk1 : k > 5:= by
                    by_contra H
                    simp at H
                    replace H : k ^ 2 ≤ 25:= by nlinarith only [H]
                    linarith
                have hk2 : k < 6:= by
                    by_contra H
                    simp at H
                    replace H : k ^ 2 ≥ 36:= by nlinarith only [H]
                    linarith
                linarith
        -- Prove that k must be odd
        have h2 : Odd k:= by
            by_contra H
            simp at H
            replace H : ∃ t : ℕ, k = 2 * t:= by exact Even.exists_two_nsmul k H
            rcases H with ⟨t, ht⟩
            subst k
            ring_nf at hk
            rw [show t ^ 2 * 4 = t ^ 2 * 2 * 2 by ring_nf] at hk
            have g1 : 2 ∣ t ^ 2 * 2 * 2:= by exact Nat.dvd_mul_left 2 (t ^ 2 * 2)
            have g2 : 2 ∣ 2 ^ (n - 1):= by refine dvd_pow_self 2 (by omega)
            replace g2 : 2 ∣ n * 2 ^ (n - 1):= by exact Dvd.dvd.mul_left g2 n
            rw [hk] at g1
            omega
        -- Since k is odd, we can write k = 2t + 1 for some natural number t
        replace h2 : ∃ t : ℕ, k = 2 * t + 1:= by exact h2
        rcases h2 with ⟨t, ht⟩
        subst k
        ring_nf at hk
        rw [show n - 1 = n - 3 + 2 by omega] at hk
        rw [show 2 ^ (n - 3 + 2) = 2 ^ (n - 3) * 4 by ring_nf] at hk
        ring_nf at hk
        -- Simplify the equation to t * (t + 1) = n * 2^(n-3)
        replace hk : t * (t + 1) = n * 2 ^ (n - 3):= by ring_nf ; linarith
        -- Establish a lower bound for 2^(n+3)
        have g1 : ∀ n : ℕ, 2 ^ (n + 3) ≥ n + 8:= by
            intro n
            induction n with
            | zero =>
                simp
            | succ n ih =>
                rw [show n + 1 + 3 = n + 3 + 1 by omega]
                rw [show 2 ^ (n + 3 + 1) = 2 * 2 ^ (n + 3) by ring_nf]
                linarith
        -- Consider two cases: t is odd or t is even
        by_cases ht : Odd t
        -- Case: t is odd
        .
            have g3 : 2 ^ (n - 3) ∣ t * (t + 1):= by exact Dvd.intro_left n (id (Eq.symm hk))
            replace g3 : 2 ^ (n - 3) ∣ t + 1:= by
                zify
                zify at g3 ht
                have g2 : IsCoprime (2 : ℤ) t:= by
                    simp [IsCoprime]
                    replace ht : ∃ s : ℕ, t = 2 * s + 1:= by exact ht
                    rcases ht with ⟨s, ht⟩
                    subst t
                    simp
                    use -s, 1
                    simp
                    ring_nf
                replace g2 : IsCoprime ((2 : ℤ) ^ (n - 3)) t:= by exact IsCoprime.pow_left g2
                exact IsCoprime.dvd_of_dvd_mul_left g2 g3
            replace g3 : ∃ a : ℕ, t + 1 = 2 ^ (n - 3) * a:= by exact g3
            rcases g3 with ⟨a, g3⟩
            rw [g3] at hk
            replace hk : t * a = n:= by
                rify
                rify at hk
                replace hk : 2 ^ (n - 3) * ((↑t : ℝ) * a - n) = 0:= by linarith
                have g4 : 2 ^ (n - 3) ≠ 0:= by positivity
                simp [g4] at hk
                linarith
            have hapos : a ≥ 1:= by
                by_contra H
                simp at H
                subst a
                simp at hk
                linarith
            have g4 : a * t ≥ t:= by exact Nat.le_mul_of_pos_left t hapos
            have g5 : 2 ^ (n - 3) * a ≥ 2 ^ (n - 3):= by exact Nat.le_mul_of_pos_right (2 ^ (n - 3)) hapos
            replace g5 : n + 1 ≥ 2 ^ (n - 3):= by linarith
            -- Show that n must be exactly 5
            by_contra H
            replace H : n ≥ 6:= by omega
            specialize g1 (n - 6)
            rw [show n - 6 + 3 = n - 3 by omega] at g1
            rw [show n - 6 + 8 = n + 2 by omega] at g1
            linarith
        -- Case: t is even
        .
            simp at ht
            have g3 : 2 ^ (n - 3) ∣ t * (t + 1):= by exact Dvd.intro_left n (id (Eq.symm hk))
            replace g3 : 2 ^ (n - 3) ∣ t:= by
                zify
                zify at g3 ht
                have g2 : IsCoprime (2 : ℤ) (t + 1):= by
                    simp [IsCoprime]
                    replace ht : ∃ s : ℕ, t = s + s:= by exact ht
                    ring_nf at ht
                    rcases ht with ⟨s, ht⟩
                    subst t
                    simp
                    use -s, 1
                    simp
                replace g2 : IsCoprime ((2 : ℤ) ^ (n - 3)) (t + 1):= by exact IsCoprime.pow_left g2
                exact IsCoprime.dvd_of_dvd_mul_right g2 g3
            replace g3 : ∃ a : ℕ, t = 2 ^ (n - 3) * a:= by exact g3
            rcases g3 with ⟨a, g3⟩
            rw [g3] at hk
            replace hk : (t + 1) * a = n:= by
                rify
                rify at hk
                rw [g3]
                simp
                replace hk : 2 ^ (n - 3) * (((2 : ℝ) ^ (n - 3) * ↑a + 1) * a - n) = 0:= by linarith
                have g4 : 2 ^ (n - 3) ≠ 0:= by positivity
                simp [g4] at hk
                linarith
            have hapos : a ≥ 1:= by
                by_contra H
                simp at H
                subst a
                simp at hk
                linarith
            have g4 : a * t ≥ t:= by exact Nat.le_mul_of_pos_left t hapos
            have g5 : 2 ^ (n - 3) * a ≥ 2 ^ (n - 3):= by exact Nat.le_mul_of_pos_right (2 ^ (n - 3)) hapos
            replace g5 : n + 1 ≥ 2 ^ (n - 3):= by linarith
            -- Show that n must be exactly 5
            by_contra H
            replace H : n ≥ 6:= by omega
            specialize g1 (n - 6)
            rw [show n - 6 + 3 = n - 3 by omega] at g1
            rw [show n - 6 + 8 = n + 2 by omega] at g1
            linarith
    -- Reverse direction: if n = 5, then 2^(n-1) * n + 1 is a perfect square
    .
        intro hn1
        subst n
        simp
        use 9
        simp
