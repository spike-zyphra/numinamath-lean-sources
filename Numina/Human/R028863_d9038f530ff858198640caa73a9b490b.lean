import Mathlib
/- The real numbers $x, y$ and $z$ are not all equal and satisfy

$$
x+\frac{1}{y}=y+\frac{1}{z}=z+\frac{1}{x}=k
$$

Determine all possible values of $k$. -/

theorem algebra_607991 : {k : ℝ | (∃ x y z : ℝ, (x ≠ y ∨ y ≠ z ∨ z ≠ x) ∧ (x ≠ 0) ∧ (y ≠ 0) ∧ (z ≠ 0) ∧ (x + 1 / y = k) ∧ (y + 1 / z = k) ∧ (z + 1 / x = k))} = {1, -1} := by
    ext k
    constructor
    .
        intro h
        simp
        simp at h
        rcases h with ⟨x, y, z, hne, hx, hy, hz, h1, h2, h3⟩

        -- Prove that k - y ≠ 0 (for later division)
        have g1 : k - y ≠ 0:= by
            by_contra H
            replace H : k = y:= by linarith
            rw [H] at h2
            field_simp at h2

        -- Express x in terms of k and y
        have h4 : x = (k * y - 1) / y:= by
            field_simp at h1
            field_simp
            linarith only [h1]

        -- Prove k * y - 1 ≠ 0 (for later division)
        have g2 : k * y - 1 ≠ 0:= by
            by_contra H
            rw [H] at h4
            simp at h4
            trivial

        -- Express z in terms of k and y
        have h5 : z = 1 / (k - y):= by
            field_simp
            field_simp at h2
            linarith only [h2]

        -- Substitute expressions for x and z into the third equation
        -- After simplification, we get (k - 1)(k + 1)(y² - ky + 1) = 0
        rw [h4, h5] at h3
        field_simp at h3
        apply sub_eq_zero.2 at h3
        ring_nf at h3
        replace h3 : (k - 1) * (k + 1) * (y ^ 2 - k * y + 1) = 0:= by
            ring_nf
            exact h3

        -- Therefore, either k = 1, k = -1, or y² - ky + 1 = 0
        replace h3 : (k - 1) * (k + 1) = 0 ∨ y ^ 2 - k * y + 1 = 0:= by exact mul_eq_zero.mp h3
        rcases h3 with h3 | h3
        .
            -- Case where k = 1 or k = -1
            replace h3 : k - 1 = 0 ∨ k + 1 = 0:= by exact mul_eq_zero.mp h3
            rcases h3 with h3 | h3
            .
                left
                linarith
            .
                right
                linarith
        .
            -- Case where y² - ky + 1 = 0 (leads to contradiction with not-all-equal condition)
            replace h3 : k = y + y⁻¹:= by
                field_simp
                linarith
            rw [h3] at h1
            field_simp at h1
            by_contra H
            rcases h1 with h1 | h1
            .
                rw [h3] at h2
                field_simp at h2
                replace h2 : z = y:= by linarith
                rcases hne with hne | hne | hne
                .
                    trivial
                .
                    replace h2 : y = z:= by rw [h2]
                    trivial
                .
                    rw [←h1] at h2
                    trivial
            .
                trivial
    .
        intro h
        simp
        simp at h
        rcases h with h | h
        .
            -- Case k = 1: Using x = 2, y = -1, z = 1/2 as a solution
            subst k
            use 2
            use (-1)
            use (1 / 2)
            simp
            constructor
            .
                left
                norm_num
            .
                refine ⟨?_, ?_, ?_⟩
                all_goals
                ring_nf
        .
            -- Case k = -1: Using x = -2, y = 1, z = -1/2 as a solution
            subst k
            use (-2)
            use 1
            use (-1 / 2)
            simp
            constructor
            .
                left
                norm_num
            .
                refine ⟨?_, ?_, ?_⟩
                all_goals
                ring_nf