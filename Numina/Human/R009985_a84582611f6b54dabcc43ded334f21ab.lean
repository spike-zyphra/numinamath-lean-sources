import Mathlib
/- Soit n un entier vérifiant $\mathrm{n} \geqslant 2$. On note d le plus grand diviseur de n différent de n . On suppose que $\mathrm{d}>1$. Démontrer que $\mathrm{n}+\mathrm{d}$ n'est pas une puissance de 2 . -/
theorem number_theory_607183 {n d : ℕ} (hn : n ≥ 2) (hd : d ∣ n) (h : ∀ k : ℕ, k ∣ n ∧ k ≠ n → k ≤ d) (h1 : d < n) (h2 : ∃ t : ℕ, n + d = 2 ^ t) (h3 : d > 1): False:= by
    -- Extract the exponent t from the hypothesis that n + d = 2^t
    rcases h2 with ⟨t, ht⟩
    -- Since d divides n, there exists s such that n = d * s
    replace hd : ∃ s : ℕ, n = d * s:= by exact hd
    rcases hd with ⟨s, hs⟩
    -- Rewrite n + d as d * s + d
    rw [show n + d = d * s + d by rw [hs]] at ht
    -- Rewrite d * s + d as d * (s + 1)
    rw [show d * s + d = d * (s + 1) by ring] at ht
    -- Since d * (s + 1) = 2^t, d divides 2^t
    have h2 : d ∣ 2 ^ t:= by rw [←ht] ; simp
    -- If d divides 2^t, then d must be a power of 2
    replace h2 : ∃ r : ℕ, r ≤ t ∧ d = 2 ^ r:= by refine (Nat.dvd_prime_pow (by decide)).mp h2
    rcases h2 with ⟨r, hr1, hr2⟩
    subst d
    -- Since d > 1, we have r ≠ 0
    replace h3 : r ≠ 0:= by
        by_contra H
        subst r
        simp at h3
    -- Prove that 2^(r-1) * s divides n
    have h5 : 2 ^ (r - 1) * s ∣ n:= by
        rw [hs]
        rw [show 2 ^ r = 2 ^ (1 + (r - 1)) by rw [show 1 + (r - 1) = r by omega]]
        rw [show 2 ^ (1 + (r - 1)) * s = 2 * (2 ^ (r - 1) * s) by ring]
        simp
    -- Prove that 2^(r-1) * s ≠ n
    have h4 : 2 ^ (r - 1) * s ≠ n:= by
        by_contra H
        rw [hs] at H
        rw [show 2 ^ r = 2 ^ (1 + (r - 1)) by rw [show 1 + (r - 1) = r by omega]] at H
        rw [show 2 ^ (1 + (r - 1)) * s = 2 * (2 ^ (r - 1) * s) by ring] at H
        replace H : 2 ^ (r - 1) * s = 0:= by linarith
        simp at H
        subst s
        simp at hs
        linarith
    -- Apply hypothesis h to 2^(r-1) * s
    replace h4:= h (2 ^ (r - 1) * s) ⟨h5, h4⟩
    -- Derive that 2 * (2^(r-1) * s) ≤ 2 * 2^r
    replace h4 : 2 * (2 ^ (r - 1) * s) ≤ 2 * 2 ^ r:= by linarith
    -- Simplify the inequality
    rw [show 2 * (2 ^ (r - 1) * s) = 2 ^ (1 + (r - 1)) * s by ring_nf] at h4
    rw [show 1 + (r - 1) = r by omega] at h4
    rw [show 2 * 2 ^ r = 2 ^ r * 2 by ring] at h4
    -- Since 2^r > 0, we can divide both sides by 2^r
    have g1 : 2 ^ r > 0:= by positivity
    replace h4 : s ≤ 2:= by exact Nat.le_of_mul_le_mul_left h4 g1
    -- Therefore s must be 0, 1, or 2
    replace h4 : s = 0 ∨ s = 1 ∨ s = 2:= by omega
    -- Consider each case for s
    rcases h4 with h4 | h4 | h4
    -- Case s = 0
    .
        subst s
        simp at hs
        linarith
    -- Case s = 1
    .
        subst s
        simp at hs
        linarith
    -- Case s = 2
    .
        subst s
        simp at ht
        -- If s = 2, then 3 divides 2^t
        replace ht : 3 ∣ 2 ^ t:= by rw [←ht] ; simp
        -- 3 is prime
        have g2 : Nat.Prime 3:= by norm_num
        -- If 3 divides 2^t, then 3 divides 2, which is a contradiction
        replace ht : 3 ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow g2 ht
        omega
