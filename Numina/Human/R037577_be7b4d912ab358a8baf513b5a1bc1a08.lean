import Mathlib
/- Do there exist positive integers $a>b>1$ such that for each positive integer $k$ there exists a positive integer $n$ for which $a n+b$ is a $k$ th power of a positive integer? -/
theorem number_theory_240499 : ∃ a b : ℕ, a > b ∧ b > 1 ∧ ∀ k : ℕ, 0 < k → ∃ n : ℕ, 0 < n ∧ ∃ m : ℕ, 0 < m ∧ m ^ k = a * n + b:= by
    -- We choose a = 6 and b = 3 as our solution
    use 6, 3
    simp
    intro k hk
    -- Define function f(n) = 6n + 3
    set f:= fun n => 6 * n + 3 with hf
    clear_value f
    -- Prove that f(n) * f(m) = f(6nm + 3(n+m) + 1)
    have h1 : ∀ n m : ℕ, f n * f m = f (6 * n * m + 3 * (n + m) + 1):= by
        intro n m
        simp [hf]
        ring_nf
    -- Prove that for any k, there exists t such that f(t) = f(0)^(k+1)
    have h2 : ∀ k : ℕ, ∃ t : ℕ, f t = f 0 ^ (k + 1):= by
        intro k
        induction k with
        | zero =>
            use 0
            simp
        | succ k ih =>
            rcases ih with ⟨t, ht⟩
            use 3 * t + 1
            specialize h1 t 0
            rw [ht] at h1
            simp at h1
            rw [←h1]
            ring
    -- Split into two cases: k = 1 and k > 1
    by_cases h : k = 1
    .
        -- Case k = 1: use n = 1
        use 1
        simp
        subst k
        simp
    .
        -- Case k > 1: use the result from h2
        specialize h2 (k - 1)
        rw [show k - 1 + 1 = k by omega] at h2
        rcases h2 with ⟨t, ht⟩
        use t
        refine ⟨?_, ?_⟩
        .
            -- Prove that t > 0
            by_contra H
            simp at H
            subst t
            simp [hf] at ht
            replace hk : k ≥ 2:= by omega
            have H : 3 ^ k ≥ 3 ^ 2:= by refine Nat.pow_le_pow_of_le_right (by omega) hk
            linarith
        .
            -- Show that m = 3 works as our solution
            use 3
            simp
            simp [hf] at ht
            linarith
