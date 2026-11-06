import Mathlib
/- If $n$ is a positive integer such that $n^{3}+2 n^{2}+9 n+8$ is the cube of an integer, find $n$. -/
theorem algebra_608528 (n : ℤ) (hn : n > 0) : (∃ k : ℤ, k ^ 3 = n ^ 3 + 2 * n ^ 2 + 9 * n + 8) ↔ n = 7:= by
    constructor
    .
        intro h
        rcases h with ⟨k, hk⟩
        by_contra H
        replace H : n < 7 ∨ n > 7:= by exact Int.ne_iff_lt_or_gt.mp H
        have hkpos : k ≥ 0:= by
            by_contra H1
            simp at H1
            replace H1 : k ^ 3 ≤ 0:= by refine Odd.pow_nonpos (by decide) (by omega)
            have H2 : n ^ 3 + 2 * n ^ 2 + 9 * n + 8 > 0:= by positivity
            linarith
        rcases H with H | H
        .
            replace H : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6:= by omega
            rcases H with H | H | H | H | H | H
            .
                subst n
                simp at hk
                have hk1 : k > 2:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≤ 2 ^ 3:= by refine pow_le_pow_left hkpos H1 3
                    linarith
                have hk2 : k < 3:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≥ 3 ^ 3:= by refine pow_le_pow_left (by omega) hk1 3
                    linarith
                linarith
            .
                subst n
                simp at hk
                have hk1 : k > 3:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≤ 3 ^ 3:= by refine pow_le_pow_left (by omega) H1 3
                    linarith
                have hk2 : k < 4:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≥ 4 ^ 3:= by refine pow_le_pow_left (by omega) hk1 3
                    linarith
                linarith
            .
                subst n
                simp at hk
                have hk1 : k > 4:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≤ 4 ^ 3:= by refine pow_le_pow_left (by omega) H1 3
                    linarith
                have hk2 : k < 5:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≥ 5 ^ 3:= by refine pow_le_pow_left (by omega) hk1 3
                    linarith
                linarith
            .
                subst n
                simp at hk
                have hk1 : k > 5:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≤ 5 ^ 3:= by refine pow_le_pow_left (by omega) H1 3
                    linarith
                have hk2 : k < 6:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≥ 6 ^ 3:= by refine pow_le_pow_left (by omega) hk1 3
                    linarith
                linarith
            .
                subst n
                simp at hk
                have hk1 : k > 6:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≤ 6 ^ 3:= by refine pow_le_pow_left (by omega) H1 3
                    linarith
                have hk2 : k < 7:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≥ 7 ^ 3:= by refine pow_le_pow_left (by omega) hk1 3
                    linarith
                linarith
            .
                subst n
                simp at hk
                have hk1 : k > 7:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≤ 7 ^ 3:= by refine pow_le_pow_left (by omega) H1 3
                    linarith
                have hk2 : k < 8:= by
                    by_contra H1
                    simp at H1
                    replace H1 : k ^ 3 ≥ 8 ^ 3:= by refine pow_le_pow_left (by omega) hk1 3
                    linarith
                linarith
        .
            have hk1 : k > n:= by
                by_contra H1
                simp at H1
                replace H1 : k ^ 3 ≤ n ^ 3:= by refine pow_le_pow_left hkpos H1 3
                have g1 : 2 * n ^ 2 + 9 * n + 8 > 0:= by positivity
                linarith
            have hk2 : k < n + 1:= by
                by_contra H1
                simp at H1
                replace H1 : k ^ 3 ≥ (n + 1) ^ 3:= by refine pow_le_pow_left (by omega) hk1 3
                replace H : n - 7 > 0:= by omega
                have g1 : (n - 7) * (n + 1) > 0:= by positivity
                linarith
            linarith
    .
        intro h
        subst n
        simp
        use 8
        simp
