import Mathlib
/- Example 12 Let the function $f: N \rightarrow N$ be strictly increasing, and for each $n \in \mathbf{N}$, we have $f(f(n))=k n$.

Prove: For all $n \in \mathbf{N}^{*}$, we have $\frac{2 k n}{k+1} \leqslant f(n) \leqslant \frac{1}{2}(k+1) n$. -/
theorem inequalities_151248 (f : ℕ → ℕ) (k : ℕ) (h : StrictMono f)
(h1 : ∀ n, f (f n) = k * n) : ∀ n : ℕ, (2 * k * n / (k + 1 : ℚ)) ≤ f n ∧ f n ≤ ((k + 1) * n / 2 : ℚ):= by
    -- Simplify the StrictMono hypothesis to its definition
    simp [StrictMono] at h
    -- Lemma h2: If m ≥ n, then f(m) + n ≥ f(n) + m
    -- This is a key inequality that follows from strict monotonicity
    have h2 : ∀ m n : ℕ, m ≥ n → f m + n ≥ f n + m:= by
        intro m n hmn
        induction m, hmn using Nat.le_induction with
        | base =>
            omega
        | succ m _ ih =>
            specialize h (show m < m + 1 by omega)
            linarith
    -- Lemma h3: For all n, f(n) ≥ n
    -- This shows that f grows at least as fast as the identity function
    have h3 : ∀ n : ℕ, f n ≥ n:= by
        intro n
        specialize h2 n 0 (by omega)
        linarith
    -- Lemma h4: For all n, 2* f(n) ≤ (k+1)*n
    -- This establishes the upper bound on f(n)
    have h4 : ∀ n : ℕ, 2 * f n ≤ (k + 1) * n:= by
        intro n
        specialize h2 (f n) n (h3 n)
        rw [h1 n] at h2
        linarith
    -- Main proof: establish both inequalities for any n
    intro n
    constructor
    -- Prove the lower bound: (2* k*n/(k+1)) ≤ f(n)
    .
        specialize h4 (f n)
        rw [h1 n] at h4
        -- Establish that k+1 > 0 for division
        have g1 : k + 1 > 0:= by omega
        -- Convert to rational numbers for division
        qify at g1 h4
        -- Restate the goal in a form that avoids division
        suffices 2 * (↑k : ℚ) * n ≤ (f n) * (k + 1) by exact (div_le_iff₀ g1).mpr this
        linarith
    -- Prove the upper bound: f(n) ≤ ((k+1)*n/2)
    .
        specialize h4 n
        -- Convert to rational numbers
        qify at h4
        linarith
