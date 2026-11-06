import Mathlib
/- Soit $\boldsymbol{n}$ un entier strictement positif et $x \geqslant \mathrm{n}$ un réel. Montrer que $x+\frac{\mathfrak{n}}{\boldsymbol{x}} \geqslant \mathrm{n}+1$ et donner les cas d'égalité. -/
theorem inequalities_607357 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : n ≤ x) :
x + n / x ≥ n + 1 ∧ (x + n / x = n + 1 ↔ x = n):= by
    -- Prove x > 0 using the fact that n > 0 and x ≥ n
    have hxpos : x > 0:= by
        rify at hn
        linarith
    constructor
    .
        -- To prove x + n/x ≥ n + 1, multiply both sides by x (which is positive)
        suffices (x + ↑n / x) * x ≥ (↑n + 1) * x by exact le_of_mul_le_mul_right this hxpos
        -- Simplify left side to x² + n
        rw [show (x + ↑n / x) * x = x ^ 2 + ↑n by field_simp ; linarith]
        -- Prove x - 1 ≥ 0 using n ≥ 1
        have hxge1 : x - 1 ≥ 0:= by
            replace hn : n ≥ 1:= by omega
            rify at hn
            linarith
        -- Show (x-1)(x-n) ≥ 0 since both factors are non-negative
        have g1 : (x - 1) * (x - ↑n) ≥ 0:= by
            replace hx : x - ↑n ≥ 0:= by linarith
            positivity
        linarith
    .
        -- Prove the equivalence x + n/x = n + 1 ↔ x = n
        constructor
        .
            -- Forward direction: if x + n/x = n + 1, then x = n
            intro h
            replace h : (x + ↑n / x) * x = (↑n + 1) * x:= by rw [h]
            rw [show (x + ↑n / x) * x = x ^ 2 + ↑n by field_simp ; linarith] at h
            -- This equality implies (x-1)(x-n) = 0
            replace h : (x - 1) * (x - ↑n) = 0:= by linarith
            -- So either x = 1 or x = n
            replace h : x - 1 = 0 ∨ x - ↑n = 0:= by exact eq_zero_or_eq_zero_of_mul_eq_zero h
            rcases h with h | h
            .
                -- If x = 1, then n must also be 1
                replace h : x = 1:= by linarith
                subst x
                replace hx : n ≤ 1:= by
                    rify
                    exact hx
                replace hx : n = 1:= by omega
                rify at hx
                rw [hx]
            .
                -- Otherwise x = n directly
                linarith
        .
            -- Reverse direction: if x = n, then x + n/x = n + 1
            intro h
            subst x
            field_simp
