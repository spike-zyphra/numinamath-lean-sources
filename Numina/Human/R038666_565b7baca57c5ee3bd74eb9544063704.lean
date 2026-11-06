import Mathlib
/- Find all non-negative integers n for which there exist integers a and b such that n^2 = a + b and n^3 = a^2 + b^2 -/
theorem algebra_605222 (n : ℤ) :
    (n ≥ 0 ∧ ∃ a b : ℤ, n ^ 2 = a + b ∧ n ^ 3 = a ^ 2 + b ^ 2) ↔ n = 0 ∨ n = 1 ∨ n = 2 := by
        constructor
        . -- Forward direction: proving that if n satisfies the conditions, then n must be 0, 1, or 2
            -- Introduce the hypothesis that n ≥ 0 and the existence of a, b
            intro ⟨hn, h⟩
            -- Extract a, b and the equations n^2 = a + b and n^3 = a^2 + b^2
            rcases h with ⟨a, b, h1, h2⟩
            -- Key inequality: 2(a^2 + b^2) ≥ (a + b)^2
            have h3 : 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2:= by
                -- Use that (a-b)^2 is non-negative
                have h4 : (a - b) ^ 2 ≥ 0:= by positivity
                -- Linear arithmetic solver
                linarith
            -- Substitute the original equations into h3
            rw [←h1, ←h2] at h3
            -- Normalize the ring expression
            ring_nf at h3
            -- Simplify to n^3(n-2) ≤ 0
            replace h3 : n ^ 3 * (n - 2) ≤ 0:= by linarith
            -- Case analysis: either n = 0 or n > 0
            by_cases hn0 : n = 0
            . -- Case n = 0
                left
                exact hn0
            . -- Case n > 0
                -- Since n > 0, n^3 > 0
                have h4 : n ^ 3 > 0:= by positivity
                -- Therefore n ≤ 2
                replace h3 : n - 2 ≤ 0:= by exact nonpos_of_mul_nonpos_right h3 h4
                -- Integer arithmetic solver proves n = 1 or n = 2
                omega
        . -- Backward direction: proving that 0, 1, and 2 satisfy the conditions
            intro h
            -- Case analysis on n = 0 or n = 1 or n = 2
            rcases h with h | h | h
            . -- Case n = 0
                constructor
                .
                    omega
                .
                    subst n
                    use 0
                    use 0
                    simp
            . -- Case n = 1
                constructor
                .
                    omega
                .
                    subst n
                    use 0
                    use 1
                    simp
            . -- Case n = 2
                constructor
                .
                    omega
                .
                    subst n
                    use 2
                    use 2
                    omega
