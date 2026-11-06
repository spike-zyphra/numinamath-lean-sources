import Mathlib
/- Soit $a_{1}, a_{2}, \ldots$ des nombres réels strictement positifs tels que

$$
a_{n+1}^{2}+a_{n} a_{n+2} \leqslant a_{n}+a_{n+2}
$$

pour tout entier $n \geqslant 1$. Démontrer que $a_{2023} \leqslant 1$. -/
theorem algebra_605495 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
(h : ∀ n, (a (n + 1)) ^ 2 + a n * a (n + 2) ≤ a n + a (n + 2)) : a 2022 ≤ 1:= by
    -- Define b_n = a_n - 1 to transform the problem
    set b : ℕ → ℝ:= fun n => a n - 1 with hb
    clear_value b
    -- Transform the inequality in terms of b_n
    replace h : ∀ n : ℕ, b (n + 1) * (b (n + 1) + 2) + b n * b (n + 2) ≤ 0:= by
        intro n
        simp [hb]
        specialize h n
        linarith
    -- Prove that for all n ≥ 2, b_n ≤ 0 (which means a_n ≤ 1)
    have h1 : ∀ n ≥ 2, b n ≤ 0:= by
        -- Proof by contradiction
        by_contra H
        simp at H
        rcases H with ⟨n, hn, hn1⟩
        -- If the statement is false, there exist consecutive positive terms
        have h1 : ∃ m ≥ 1, b m > 0 ∧ b (m + 1) > 0:= by
            specialize h (n - 1)
            rw [show n - 1 + 1 = n by omega] at h
            rw [show n - 1 + 2 = n + 1 by omega] at h
            replace h : b (n - 1) * b (n + 1) ≤ - (b n * (b n + 2)):= by linarith
            have g1 : b n * (b n + 2) > 0:= by positivity
            -- At least one of b(n-1) or b(n+1) must be positive
            have g2 : b (n - 1) > 0 ∨ b (n + 1) > 0:= by
                by_contra H
                simp at H
                rcases H with ⟨H1, H2⟩
                replace H1 : -b (n - 1) ≥ 0:= by linarith
                replace H2 : -b (n + 1) ≥ 0:= by linarith
                have H3 : (-b (n - 1)) * (-b (n + 1)) ≥ 0:= by positivity
                linarith
            rcases g2 with g2 | g2
            .
                use (n - 1)
                refine ⟨by omega, by linarith, by rw [show n - 1 + 1 = n by omega] ; linarith⟩
            .
                use n
                refine ⟨by omega, by linarith, by linarith⟩
        -- Using the consecutive positive terms to derive a contradiction
        rcases h1 with ⟨m, hm, hm1, hm2⟩
        -- Show that b_n ≥ -1 for all n (since a_n > 0)
        replace ha : ∀ n : ℕ, b n ≥ -1:= by
            intro n
            simp [hb]
            specialize ha n
            linarith
        -- Show that b_(m+1) > b_m
        have h1 : b (m + 1) > b m:= by
            specialize h (m - 1)
            rw [show m - 1 + 1 = m by omega] at h
            rw [show m - 1 + 2 = m + 1 by omega] at h
            specialize ha (m - 1)
            replace ha : b (m - 1) + 1 ≥ 0:= by linarith
            replace ha : b (m + 1) * (b (m - 1) + 1) ≥ 0:= by positivity
            have h1 : b m * (b m + 1) > 0:= by positivity
            linarith
        -- Show that b_m > b_(m+1)
        have h2 : b m > b (m + 1):= by
            specialize h m
            specialize ha (m + 2)
            replace ha : b (m + 2) + 1 ≥ 0:= by linarith
            replace ha : b m * (b (m + 2) + 1) ≥ 0:= by positivity
            have h2 : b (m + 1) * (b (m + 1) + 1) > 0:= by positivity
            linarith
        linarith
    -- Apply the result to n = 2022
    specialize h1 2022
    replace h1:= h1 (by omega)
    simp [hb] at h1
    exact h1
