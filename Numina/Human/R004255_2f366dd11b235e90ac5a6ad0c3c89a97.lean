import Mathlib
/- Find all positive integers $n$ such that $2^{n}+12^{n}+2011^{n}$ is a perfect square. -/
theorem number_theory_245602 (n : ℕ) (hn : n > 0) : (∃ k, k ^ 2 = 2 ^ n + 12 ^ n + 2011 ^ n) ↔ n = 1:= by
    -- Split into two directions: forward and reverse implications
    constructor
    .
        -- Forward direction: if 2^n + 12^n + 2011^n is a perfect square, then n = 1
        intro h
        -- Extract the witness k from the hypothesis
        rcases h with ⟨k, hk⟩
        -- Proof by contradiction: assume n ≠ 1
        by_contra H
        -- If n ≠ 1 and n > 0, then n ≥ 2
        replace H : n ≥ 2:= by omega
        -- Split into two cases: n is even or n is odd
        by_cases h : Even n
        .
            -- Case 1: n is even
            -- Express n as 2t for some natural number t
            replace h : ∃ t : ℕ, n = t + t:= by exact h
            rcases h with ⟨t, ht⟩
            ring_nf at ht
            subst n
            -- Prove that k² cannot be congruent to 2 modulo 3
            have h1 : ¬(k ^ 2 ≡ 2 [ZMOD 3]):= by
                by_contra H1
                -- Check all possible values of k modulo 3
                mod_cases (↑k : ℤ) % 3
                all_goals
                    replace H:= Int.ModEq.pow 2 H
                    simp at H
                    apply Int.ModEq.trans (id (Int.ModEq.symm H)) at H1
                    simp [Int.ModEq] at H1
            -- Convert to integer arithmetic
            zify at hk
            -- Establish modular congruences for our terms modulo 3
            have g1 : 2 ≡ -1 [ZMOD 3]:= by rfl
            have g2 : 12 ≡ 0 [ZMOD 3]:= by rfl
            have g3 : 2011 ≡ 1 [ZMOD 3]:= by rfl
            -- Compute the congruences when raised to power n = 2t
            replace g1:= Int.ModEq.pow (t * 2) g1
            replace g2:= Int.ModEq.pow (t * 2) g2
            replace g3:= Int.ModEq.pow (t * 2) g3
            -- Combine the congruences to get the sum
            have g4:= Int.ModEq.add (Int.ModEq.add g1 g2) g3
            -- Substitute the original equation
            rw [←hk] at g4
            simp at g4
            -- Simplify 0^(t*2) to 0
            rw [show (0 : ℤ) ^ (t * 2) = 0 by exact Mathlib.Tactic.Ring.zero_pow hn] at g4
            simp at g4
            -- Derive a contradiction
            trivial
        .
            -- Case 2: n is odd
            simp at h
            -- Prove that k² cannot be congruent to -1 modulo 4
            have h1 : ¬(k ^ 2 ≡ -1 [ZMOD 4]):= by
                by_contra H1
                -- Check all possible values of k modulo 4
                mod_cases (↑k : ℤ) % 4
                all_goals
                    replace H:= Int.ModEq.pow 2 H
                    simp at H
                    apply Int.ModEq.trans (id (Int.ModEq.symm H)) at H1
                    simp [Int.ModEq] at H1
            -- Convert to integer arithmetic
            zify at hk
            -- Show that 2^n ≡ 0 (mod 4) when n ≥ 2
            have g1 : 2 ^ n ≡ 0 [ZMOD 4]:= by
                rw [show n = 2 + (n - 2) by omega]
                rw [show (2 : ℤ) ^ (2 + (n - 2)) = 4 * (2 : ℤ) ^ (n - 2) by ring]
                have g1 : 4 ≡ 0 [ZMOD 4]:= by rfl
                replace g1 : 4 * 2 ^ (n - 2) ≡ 0 * 2 ^ (n - 2)[ZMOD 4]:= by exact Int.ModEq.mul g1 rfl
                simp at g1
                exact g1
            -- Establish that 12 ≡ 0 (mod 4)
            have g2 : 12 ≡ 0 [ZMOD 4]:= by rfl
            replace g2:= Int.ModEq.pow n g2
            -- Simplify 0^n to 0
            rw [show (0 : ℤ) ^ n = 0 by exact Mathlib.Tactic.Ring.zero_pow hn] at g2
            -- Establish that 2011 ≡ -1 (mod 4)
            have g3 : 2011 ≡ -1 [ZMOD 4]:= by rfl
            replace g3:= Int.ModEq.pow n g3
            -- Use the fact that (-1)^n = -1 when n is odd
            rw [show (-1 : ℤ) ^ n = -1 by exact Odd.neg_one_pow h] at g3
            -- Combine the congruences to get the sum
            have g4:= Int.ModEq.add (Int.ModEq.add g1 g2) g3
            -- Substitute the original equation
            rw [←hk] at g4
            simp at g4
            -- Derive a contradiction
            trivial
    .
        -- Reverse direction: if n = 1, then 2^n + 12^n + 2011^n is a perfect square
        intro h
        subst n
        -- When n = 1, the sum is 2 + 12 + 2011 = 2025 = 45²
        use 45
        simp
