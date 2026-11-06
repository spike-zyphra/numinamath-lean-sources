import Mathlib

/- Given a sequence $a_{1}, a_{2}, a_{3}, \ldots$ of non-negative real numbers satisfying the conditions

(1) $a_{n}+a_{2 n} \geq 3 n$

(2) $a_{n+1}+n \leq 2 \sqrt{a_{n} \cdot(n+1)}$

for all indices $n=1,2 \ldots$

(a) Prove that the inequality $a_{n} \geq n$ holds for every $n \in \mathbb{N}$.

(b) Give an example of such a sequence. -/

theorem inequalities_239333 (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (h1 : ∀ n, a n + a (2 * n) ≥ 3 * n) (h2 : ∀ n, a (n + 1) + n ≤ 2 * √(a n * (n + 1))) : (∀ n, a n ≥ n) ∧ ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ (∀ n, a n + a (2 * n) ≥ 3 * n) ∧ (∀ n, a (n + 1) + n ≤ 2 * √(a n * (n + 1))) ∧ (∀ n, a n ≥ n):= by

    -- Split the proof into two parts
    constructor
    .
        -- Part (a): Prove that a_n ≥ n for all n
        intro n
        -- Case split on whether n = 0
        by_cases hn : n = 0
        .
            -- Case n = 0
            subst n
            simp
            specialize h1 0
            simp at h1
            exact h1
        .
            -- Case n > 0
            replace hn : n > 0:= by omega
            -- Key lemma: Prove that a_(n+1)/a_n ≤ (n+1)/n for all positive n
            have h3 : ∀ n : ℕ, n > 0 → a (n + 1) / a n ≤ (n + 1) / n:= by
                intro m hm
                specialize h2 m
                -- Prove that a_(m+1) + m ≥ 2√(a_(m+1)m)
                have h3 : a (m + 1) + m ≥ 2 * √(a (m + 1) * m):= by
                    have h3 : (√(a (m + 1)) - √m) ^ 2 ≥ 0:= by positivity
                    ring_nf at h3
                    rw [show √(a (1 + m)) ^ 2 = a (1 + m) by exact Real.sq_sqrt (ha (1 + m))] at h3
                    rw [show √m ^ 2 = m by exact Real.sq_sqrt (by linarith)] at h3
                    ring_nf
                    rw [show √(a (1 + m)) * √↑m = √(a (1 + m) * ↑m) by field_simp] at h3
                    linarith
                replace h3 : √(a (m + 1) * m) ≤ √(a m * (m + 1)):= by linarith
                have g1:= ha m
                have g2:= ha (m + 1)
                replace h3 : a (m + 1) * m ≤ a m * (m + 1):= by exact (Real.sqrt_le_sqrt_iff (by positivity)).mp h3
                -- Handle the case where a_(m+1) = 0
                by_cases ham : a (m + 1) = 0
                .
                    rw [ham]
                    simp
                    positivity
                .
                    replace g2 : 0 < a (m + 1):= by positivity
                    clear ham
                    -- Prove a_m > 0
                    replace g1 : 0 < a m:= by
                        by_contra H
                        simp at H
                        replace H : a m = 0:= by linarith
                        rw [H] at h3
                        simp at h3
                        have g3 : a (m + 1) * m > 0:= by positivity
                        linarith
                    suffices a (m + 1) ≤ (m + 1) / m * a m by exact (div_le_iff₀ g1).mpr this
                    field_simp
                    rify at hm
                    suffices (m + 1) * a m ≥ a (m + 1) * m by exact (le_div_iff₀ hm).mpr this
                    linarith
            -- Prove that a_n > 0 for all positive n
            have hpos : ∀ n : ℕ, n > 0 → a n > 0:= by
                intro m hm
                specialize h2 m
                have g1:= ha m
                have g2:= ha (m + 1)
                by_contra H
                simp at H
                replace H : a m = 0:= by linarith
                rw [H] at h2
                simp at h2
                rify at hm
                linarith
            -- Extend the ratio inequality to multiple steps
            replace h3 : ∀ n : ℕ, n > 0 → ∀ k : ℕ, a (n + k + 1) / a n ≤ (n + k + 1) / n:= by
                intro n hn k
                induction k with
                | zero =>
                    simp
                    specialize h3 n hn
                    exact h3
                | succ k hk =>
                    rw [show n + (k + 1) + 1 = n + k + 2 by ring]
                    specialize h3 (n + k + 1) (by linarith)
                    rw [show n + k + 1 + 1 = n + k + 2 by ring] at h3
                    specialize hpos (n + k + 1) (by linarith)
                    simp at h3 hk
                    simp
                    have g1:= ha (n + k + 1)
                    have g2:= ha (n + k + 2)
                    simp at g1 g2
                    rw [show a (n + k + 2) / a n = a (n + k + 2) / a (n + k + 1) * (a (n + k + 1) / a n) by field_simp]
                    rw [show (↑n : ℝ) + (↑k + 1) + 1 = (↑n : ℝ) + ↑k + 1 + 1 by ring]
                    rw [show ((↑n : ℝ) + ↑k + 1 + 1) / ↑n = (↑n + ↑k + 1 + 1) / (↑n + ↑k + 1) * ((↑n + ↑k + 1) / ↑n) by field_simp]
                    refine mul_le_mul_of_nonneg h3 hk (by positivity) (by positivity)
            -- Apply the ratio inequality to prove a_n ≥ n
            specialize h3 n hn (n - 1)
            rw [show n + (n - 1) + 1 = 2 * n by omega] at h3
            have g1 : n + (n - 1) + 1 = 2 * n:= by omega
            rify at g1
            rw [g1] at h3
            rw [show (2 : ℝ) * n / n = 2 by field_simp] at h3
            specialize hpos n hn
            replace h3 : a (2 * n) ≤ 2 * a n:= by exact (mul_inv_le_iff₀ hpos).mp h3
            specialize h1 n
            linarith
    .
        -- Part (b): Provide an example sequence a_n = n + 1
        use fun n => n + 1
        simp
        refine ⟨?_, ?_, ?_⟩
        .
            -- Prove non-negativity
            intro n
            linarith
        .
            -- Prove condition (1)
            intro n
            linarith
        .
            -- Prove condition (2)
            intro n
            field_simp
            linarith
