import Mathlib
/- The function $\mathrm{f}$ is defined on the non-negative integers. $\mathrm{f}\left(2^{\mathrm{n}}-1\right)=0$ for $\mathrm{n}=0,1,2, \ldots$. If $\mathrm{m}$ is not of the form $2^{n}-1$, then $f(m)=f(m+1)+1$. Show that $f(n)+n=2^{k}-1$ for some $k$, and find $\mathrm{f}\left(2^{1990}\right)$ -/
theorem number_theory_604340 (f : ℕ → ℕ) (h1 : ∀ n, f (2 ^ n - 1) = 0) (h2 : ∀ m, (¬∃ n, m = 2 ^ n - 1) → f m = f (m + 1) + 1) :
(∀ n : ℕ, (∃ k, f n + n = 2 ^ k - 1)) ∧ f (2 ^ 1990) = 2 ^ 1990 - 1:= by
    -- Reformulate h2 to work with numbers in specific ranges
    -- For any m in range [2^n, 2^(n+1)-2], we have f(m) = f(m+1) + 1
    replace h2 : ∀ m : ℕ, (∃ n, (2 ^ n ≤ m  ∧ m < 2 ^ (n + 1) - 1)) → f m = f (m + 1) + 1:= by
        intro m h
        rcases h with ⟨n, hn1, hn2⟩
        -- Prove that m is not of the form 2^n - 1
        have g1 : ¬∃ n, m = 2 ^ n - 1:= by
            by_contra H
            rcases H with ⟨a, ha⟩
            -- If m = 2^a - 1, then a must be between n and n+1, which is impossible
            have g1 : a < n + 1:= by
                by_contra H
                simp at H
                replace H : 2 ^ (n + 1) ≤ 2 ^ a:= by refine Nat.pow_le_pow_of_le_right (by omega) H
                replace H : 2 ^ (n + 1) - 1 ≤ 2 ^ a - 1:= by omega
                linarith
            have g2 : a > n:= by
                by_contra H
                simp at H
                replace H : 2 ^ a ≤ 2 ^ n:= by refine Nat.pow_le_pow_of_le_right (by omega) H
                omega
            linarith
        specialize h2 m g1
        exact h2
    -- Set l to 1990 for later use
    set l:= 1990 with hl
    clear_value l
    -- Key lemma: for any m and r ≤ 2^m - 1, f(2^(m+1) - r - 1) = r
    have h3 : ∀ m : ℕ, ∀ r : ℕ, r ≤ 2 ^ m - 1 → f (2 ^ (m + 1) - r - 1) = r:= by
        intro m r
        induction r with
        -- Base case: r = 0
        | zero =>
            intro _
            simp
            rw [h1]
        -- Inductive step: assume true for r, prove for r+1
        | succ r ih =>
            intro hr
            specialize h2 (2 ^ (m + 1) - (r + 1) - 1)
            -- Prove that 2^(m+1) - (r+1) - 1 is in the range [2^m, 2^(m+1)-2]
            have g1 : ∃ n, 2 ^ n ≤ 2 ^ (m + 1) - (r + 1) - 1 ∧ 2 ^ (m + 1) - (r + 1) - 1 < 2 ^ (n + 1) - 1:= by
                use m
                constructor
                .
                    rw [show 2 ^ (m + 1) = 2 * 2 ^ m by ring]
                    suffices 2 ^ m + 1 + (r + 1) ≤ 2 * 2 ^ m by omega
                    omega
                .
                    rw [show 2 ^ (m + 1) = 2 * 2 ^ m by ring]
                    omega
            specialize h2 g1
            clear g1
            rw [h2]
            rw [show 2 ^ (m + 1) - (r + 1) - 1 + 1 = 2 ^ (m + 1) - (r + 1) by omega]
            replace ih:= ih (by omega)
            rw [show 2 ^ (m + 1) - r - 1 = 2 ^ (m + 1) - (r + 1) by omega] at ih
            rw [ih]
    -- Now prove both parts of the theorem
    constructor
    -- First part: For all n, there exists k such that f(n) + n = 2^k - 1
    .
        intro n
        by_cases h : n = 0
        -- Case n = 0
        .
            subst n
            use 0
            simp
            specialize h1 0
            simp at h1
            exact h1
        -- Case n ≥ 1
        .
            replace h : n ≥ 1:= by omega
            -- Let t be the floor of log_2(n)
            set t:= ⌊Real.logb 2 n⌋.natAbs with ht
            clear_value t
            -- Prove that 2^t ≤ n < 2^(t+1)
            have ht1 : 2 ^ t ≤ n:= by
                rify
                rw [show (2 : ℝ) ^ t = 2 ^ (↑t : ℝ) by norm_cast]
                suffices t ≤ Real.logb 2 n by refine (Real.le_logb_iff_rpow_le (by linarith) (by simp ; omega)).mp this
                rw [show (↑t : ℝ) = (↑(↑t : ℤ) : ℝ) by norm_cast]
                rw [ht]
                simp
                have g1 : Real.logb 2 n ≥ 0:= by refine Real.logb_nonneg (by linarith) (by simp ; linarith)
                replace g1 : ⌊Real.logb 2 n⌋ ≥ 0:= by exact Int.floor_nonneg.mpr g1
                rw [abs_of_nonneg _]
                exact Int.floor_le (Real.logb 2 ↑n)
                simp
                linarith
            have ht2 : n < 2 ^ (t + 1):= by
                rify
                rw [show (2 : ℝ) ^ (t + 1) = 2 ^ (t + (1 : ℝ)) by norm_cast]
                suffices Real.logb 2 n < t + 1 by refine (Real.logb_lt_iff_lt_rpow (by linarith) (by simp ; omega)).mp this
                rw [show (↑t : ℝ) = (↑(↑t : ℤ) : ℝ) by norm_cast]
                rw [ht]
                simp
                have g1 : |↑(⌊Real.logb 2 ↑n⌋ : ℝ)| ≥ ↑⌊Real.logb 2 ↑n⌋:= by exact le_abs_self ↑(⌊Real.logb 2 ↑n⌋ : ℝ)
                have g2 : Real.logb 2 ↑n - 1 < ↑⌊Real.logb 2 ↑n⌋:= by exact Int.sub_one_lt_floor (Real.logb 2 ↑n)
                linarith
            -- Apply lemma h3 to find f(n)
            specialize h3 t (2 ^ (t + 1) - n - 1) (by omega)
            rw [show 2 ^ (t + 1) - (2 ^ (t + 1) - n - 1) - 1 = n by omega] at h3
            use (t + 1)
            omega
    -- Second part: f(2^1990) = 2^1990 - 1
    .
        specialize h3 l (2 ^ l - 1) (by omega)
        rw [show 2 ^ (l + 1) - (2 ^ l - 1) - 1 = 2 ^ l by rw [show 2 ^ (l + 1) = 2 * 2 ^ l by ring] ; omega] at h3
        exact h3
