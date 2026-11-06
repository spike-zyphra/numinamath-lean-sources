import Mathlib
/- Soit $n \geqslant 1$ un entier tel que le quotient de $2^{n}$ par $n$ est une puissance de 2 . Montrer que $n$ est une puissance de 2 . -/
theorem number_theory_607564 (n : ℕ) (h : ∃ k : ℕ, 2 ^ n = 2 ^ k * n) : ∃ t : ℕ, n = 2 ^ t:= by
    -- Extract the witness k from the hypothesis
    rcases h with ⟨k, hk⟩

    -- Prove that n ≥ 1
    have hnpos : n ≥ 1:= by
        by_contra H
        simp at H
        subst n
        simp at hk

    -- Prove that k ≤ n
    have hkle : k ≤ n:= by
        by_contra H
        -- If k > n, then k ≥ n + 1
        replace H : k ≥ n + 1:= by omega
        -- This implies 2^k ≥ 2^(n+1)
        replace H : 2 ^ k ≥ 2 ^ (n + 1):= by refine Nat.pow_le_pow_of_le_right (by omega) H
        -- Multiply both sides by n
        replace H : 2 ^ k * n ≥ 2 ^ (n + 1) * n:= by exact Nat.mul_le_mul_right n H
        -- Rewrite 2^(n+1) as 2 * 2^n
        rw [show 2 ^ (n + 1) = 2 * 2 ^ n by ring] at H
        -- Substitute the original equation
        rw [←hk] at H
        -- Since n ≥ 1, we have 2 * 2^n * n ≥ 2 * 2^n
        have h1 : 2 * 2 ^ n * n ≥ 2 * 2 ^ n:= by exact Nat.le_mul_of_pos_right (2 * 2 ^ n) hnpos
        -- This leads to a contradiction
        replace H : 2 ^ n ≤ 0:= by linarith
        simp at H

    -- Rewrite 2^n using n-k+k = n
    rw [show 2 ^ n = 2 ^ ((n - k) + k) by rw [show n - k + k = n by omega]] at hk
    -- Use the property of exponents: 2^(a+b) = 2^a * 2^b
    rw [show 2 ^ ((n - k) + k) = 2 ^ (n - k) * 2 ^ k by ring] at hk
    -- Prove that n = 2^(n-k)
    replace hk : n = 2 ^ (n - k):= by
        zify at hk
        zify
        replace hk : (2 : ℤ) ^ k * (n - 2 ^ (n - k)) = 0:= by linarith
        simp at hk
        linarith

    -- Conclude that n = 2^t where t = n-k
    use (n - k)
