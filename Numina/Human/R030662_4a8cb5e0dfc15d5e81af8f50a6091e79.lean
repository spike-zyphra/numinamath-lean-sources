import Mathlib
/- Eine Funktion $f$ ist gegeben durch $f(x)+f\left(1-\frac{1}{x}\right)=1+x$ für $x \in \mathbb{R} \backslash\{0,1\}$.
Man ermittle eine Formel für $f$. -/
theorem algebra_606074 {f : ℝ → ℝ} : (∀ x, x ≠ 0 ∧ x ≠ 1 → f x + f (1 - 1 / x) = 1 + x) ↔ ∀ x, x ≠ 0 ∧ x ≠ 1 → f x = (-x ^ 3 + x ^ 2 + 1) / (2 * x * (1 - x)):= by

    -- Start with both directions of the proof
    constructor
    .
        -- Forward direction: assuming the functional equation, prove the explicit formula
        intro h
        intro x hx
        rcases hx with ⟨hx1, hx2⟩

        -- Prove that 1-1/x is neither 0 nor 1
        have hx3 : 1 - 1 / x ≠ 0 ∧ 1 - 1 / x ≠ 1:= by
            constructor
            .
                by_contra H
                field_simp at H
                replace H : x = 1:= by linarith
                trivial
            .
                by_contra H
                field_simp at H
        rcases hx3 with ⟨hx3, hx4⟩
        -- Prove that 1/(1-x) is neither 0 nor 1
        have hx5 : 1 / (1 - x) ≠ 0 ∧ 1 / (1 - x) ≠ 1:= by
            constructor
            .
                by_contra H
                field_simp at H
                replace H : x = 1:= by linarith
                trivial
            .
                by_contra H
                replace hx2 : 1 - x ≠ 0:= by
                    by_contra H
                    replace H : x = 1:= by linarith
                    trivial
                field_simp at H
                replace H : x = 0:= by linarith
                trivial

        -- Apply the functional equation at different points
        rcases hx5 with ⟨hx5, hx6⟩
        have h1:= h x ⟨hx1, hx2⟩
        have h2:= h (1 - 1 / x) ⟨hx3, hx4⟩
        have h3:= h (1 / (1 - x)) ⟨hx5, hx6⟩

        -- Prove x ≠ 1 in a different form
        have g1 : 1 - x ≠ 0:= by
            by_contra H
            replace H : x = 1:= by linarith
            trivial

        -- Simplify and manipulate equations
        field_simp at h1 h2 h3
        have g2 : x - 1 ≠ 0:= by
            by_contra H
            replace H : x = 1:= by linarith
            trivial

        -- Series of algebraic manipulations and substitutions
        rw [show 1 - x / (x - 1) = 1 / (1 - x) by field_simp] at h2
        rw [show x + (x - 1) = 2 * x - 1 by ring] at h2
        rw [show 1 - x + 1 = 2 - x by ring] at h3

        -- Derive the final formula through algebraic manipulations
        replace h2 : f ((x - 1) / x) + f (1 / (1 - x)) = (2 * x - 1) / x:= by
            field_simp
            linarith
        replace h3 : f (1 / (1 - x)) + f x = (2 - x) / (1 - x):= by
            field_simp
            linarith
        have h4 : f x = (1 + x + (2 - x) / (1 - x) - (2 * x - 1) / x) / 2:= by
            rw [←h1, ←h2, ←h3]
            linarith
        rw [h4]
        field_simp
        linarith
    .
        -- Backward direction: proving the functional equation from the explicit formula
        intro h
        intro x hx
        have g1:= h x hx
        rcases hx with ⟨hx1, hx2⟩
        have h1 : 1 - 1 / x ≠ 0 ∧ 1 - 1 / x ≠ 1:= by
            constructor
            .
                by_contra H
                field_simp at H
                replace H : x = 1:= by linarith
                trivial
            .
                by_contra H
                field_simp at H
        have g2:= h (1 - 1 / x) h1
        rw [g1, g2]
        have g3 : x - 1 ≠ 0:= by
            by_contra H
            replace H : x = 1:= by linarith
            trivial
        have g4 : 1 - x ≠ 0:= by
            by_contra H
            replace H : x = 1:= by linarith
            trivial
        field_simp
        linarith
