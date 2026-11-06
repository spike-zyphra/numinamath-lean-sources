import Mathlib
/- a) Prouver que, pour tous réels strictement positifs $a, b, k$ tels que $a< b$, on a

$$
\frac{a}{b}<\frac{a+k}{b+k}
$$

b) Prouver que

$$
\frac{1}{100}+\frac{4}{101}+\frac{7}{102}+\frac{10}{103}+\cdots+\frac{148}{149}>25
$$ -/

theorem algebra_604918 : (∀ a b k : ℝ, a > 0 → b > 0 → a < b → k > 0 → a / b < (a + k) / (b + k)) ∧ (∑ i in Finset.range (50), (1 + 3 * (↑i : ℝ)) / (100 + ↑i) > 25):= by
    -- Part 1: Prove the fraction inequality
    have h1 : ∀ a b k : ℝ, a > 0 → b > 0 → a < b → k > 0 → a / b < (a + k) / (b + k):= by
        intro a b k _ hb hab hk
        -- Prove b*(b+k) > 0 for later use
        have g1 : b * (b + k) > 0:= by positivity
        -- Main proof strategy: multiply both sides by b*(b+k)
        suffices (a / b) * (b * (b + k)) < ((a + k) / (b + k)) * (b * (b + k)) by exact (mul_lt_mul_iff_of_pos_right g1).mp this
        -- Simplify left side using field operations
        rw [show (a / b) * (b * (b + k)) = a * (b + k) by field_simp ; linarith]
        -- Simplify right side using field operations
        rw [show ((a + k) / (b + k)) * (b * (b + k)) = (a + k) * b by field_simp ; linarith]
        -- Use the fact that b-a > 0
        replace hab : b - a > 0:= by linarith
        -- Show (b-a)*k > 0
        replace hab : (b - a) * k > 0:= by positivity
        linarith
    constructor
    .
        exact h1
    .
        -- Part 2: Prove the sum inequality
        -- Inductive step: prove sum up to m+2 terms is greater than simpler sum
        replace h1 : ∀ m : ℕ, m ≤ 48 → ∑ i ∈ Finset.range (m + 2), (1 + 3 * (↑i : ℝ)) / (100 + ↑i) > ∑ i ∈ Finset.range (m + 2), (1 + 2 * (↑i : ℝ)) / 100:= by
            intro m
            induction m with
            -- Base case: m = 0
            | zero =>
                simp [Finset.sum_range_succ]
                norm_num
            -- Inductive case
            | succ m ih =>
                intro hm
                rw [show m + 1 + 2 = m + 2 + 1 by ring_nf]
                set n:= m + 2 with hn
                clear_value n
                replace ih:= ih (by omega)
                simp [Finset.sum_range_succ]
                -- Establish bounds for n
                have hn1 : n ≥ 2:= by omega
                replace hn : n ≤ 49:= by omega
                rify at hn hn1
                -- Apply the fraction inequality from part 1
                specialize h1 (1 + 2 * (↑n : ℝ)) 100 (↑n : ℝ) (by linarith) (by linarith) (by linarith) (by linarith)
                rw [show 1 + 2 * (↑n : ℝ) + ↑n = 1 + 3 * (↑n : ℝ) by ring_nf] at h1
                linarith
        -- Apply the result to m = 48 to get all 50 terms
        specialize h1 48 (by omega)
        rw [show 48 + 2 = 50 by ring_nf] at h1
        -- Show that the simpler sum equals 25
        have h2 : ∑ i ∈ Finset.range 50, (1 + 2 * (↑i : ℝ)) / 100 = 25:= by ring_nf
        linarith
