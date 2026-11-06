import Mathlib
/- Solve over $\mathbb{R}$ the functional equation $f\left(x^{2}-y\right)+2 y f(x)=f(f(x))+f(y)$. -/
theorem algebra_246362 : {f : ℝ → ℝ | ∀ x y, f (x ^ 2 - y) + 2 * y * f x = f (f x) + f y} = {f : ℝ → ℝ | (∀ x, f x = x ^ 2) ∨ (∀ x, f x = 0) ∨ (∀ x, f x = -x ^ 2)} := by
    ext f
    constructor
    .
        -- Forward direction: proving that any function satisfying the functional equation
        -- must be one of the three specified functions
        intro h
        simp at h
        -- First, we prove that f(0) = 0
        have h1 : f 0 = 0:= by
            have h1:= h 1 0
            have h2:= h 1 (1 / 2)
            norm_num at h1 h2
            linarith
        -- Next, we prove that f is an even function: f(x) = f(-x) for all x
        have h2 : ∀ x : ℝ, f x = f (-x):= by
            intro x
            specialize h 0 x
            ring_nf at h
            rw [h1] at h
            rw [h1] at h
            linarith
        -- We now prove that for any x, f(x) must be either 0, x², or -x²
        have h3 : ∀ x : ℝ, f x = 0 ∨ f x = x ^ 2 ∨ f x = -x ^ 2:= by
            intro x
            by_cases hx : x = 0
            .
                -- Case: x = 0
                subst x
                rw [h1]
                simp
            .
                -- Case: x ≠ 0
                by_cases hx1 : f x = 0
                .
                    -- Subcase: f(x) = 0
                    simp [hx1]
                .
                    -- Subcase: f(x) ≠ 0
                    -- We set y = √|x| and derive properties of f
                    replace hx : |x| ≠ 0:= by exact abs_ne_zero.mpr hx
                    set y:= √|x| with hy
                    clear_value y
                    replace hx1 : f (y ^ 2) ≠ 0:= by
                        subst y
                        field_simp
                        by_contra H
                        by_cases hx2 : x < 0
                        .
                            rw [abs_of_neg hx2] at H
                            rw [←h2 x] at H
                            trivial
                        .
                            simp at hx2
                            rw [abs_of_nonneg hx2] at H
                            trivial
                    -- We derive several key properties from the functional equation
                    have g1 : ∀ x : ℝ, x ^ 2 * f x = f (f x):= by
                        intro x
                        specialize h x (x ^ 2 / 2)
                        ring_nf at h
                        linarith
                    have g2 : ∀ x : ℝ, f (x ^ 2) = f (f x):= by
                        intro x
                        specialize h x 0
                        simp at h
                        linarith
                    -- We apply these properties to specific values
                    have g3:= g1 (y ^ 2)
                    have g4:= g2 (y ^ 2)
                    have g5:= g1 (f y)
                    have g6:= g2 (f y)
                    replace g1:= g1 y
                    replace g2:= g2 y
                    -- We derive two different expressions for f(f(f(y)))
                    have h3 : f (f (f y)) = y ^ 4 * f (y ^ 2):= by
                        rw [←g2, ←g4]
                        ring_nf at g4 ⊢
                        rw [g4, ←g3]
                        ring_nf
                    have h4 : f (f (f y)) = f y ^ 2 * f (y ^ 2):= by rw [←g5, ←g2]
                    -- Comparing these expressions leads to a key equation
                    replace h3 : f (y ^ 2) * (f y - y ^ 2) * (f y + y ^ 2) = 0:= by linarith
                    simp [hx1] at h3
                    rcases h3 with h3 | h3
                    .
                        -- Case: f(y) = y²
                        replace h3 : f y = y ^ 2:= by linarith
                        rw [←g1] at g2
                        rw [h3] at g2
                        subst y
                        field_simp at g2
                        by_cases hx2 : x < 0
                        .
                            rw [abs_of_neg hx2] at g2
                            rw [←h2 x] at g2
                            ring_nf at g2
                            simp [g2]
                        .
                            simp at hx2
                            rw [abs_of_nonneg hx2] at g2
                            ring_nf at g2
                            simp [g2]
                    .
                        -- Case: f(y) = -y²
                        replace h3 : f y = -y ^ 2:= by linarith
                        rw [←g1] at g2
                        rw [h3] at g2
                        subst y
                        field_simp at g2
                        by_cases hx2 : x < 0
                        .
                            rw [abs_of_neg hx2] at g2
                            rw [←h2 x] at g2
                            ring_nf at g2
                            simp [g2]
                        .
                            simp at hx2
                            rw [abs_of_nonneg hx2] at g2
                            ring_nf at g2
                            simp [g2]
        -- We determine the value of f(1) to narrow down which of the three functions f is
        have g1:= h3 1
        simp at g1
        -- We derive another key property from the functional equation
        have g2 : ∀ x y : ℝ, y ^ 2 * f x = x ^ 2 * f y:= by
            intro x y
            have g2:= h x (y ^ 2)
            have g3:= h y (x ^ 2)
            have g4:= h x 0
            have g5:= h y 0
            ring_nf at g4 g5
            rw [h1] at g4 g5
            simp at g4 g5
            rw [g4] at g3
            rw [g5] at g2
            specialize h2 (x ^ 2 - y ^ 2)
            simp at h2
            linarith
        -- Based on the value of f(1), we determine which of the three functions f is
        simp
        rcases g1 with g1 | g1 | g1
        .
            -- Case: f(1) = 0, which implies f(x) = 0 for all x
            right
            left
            intro x
            specialize g2 x 1
            rw [g1] at g2
            simp at g2
            linarith
        .
            -- Case: f(1) = 1, which implies f(x) = x² for all x
            left
            intro x
            specialize g2 x 1
            rw [g1] at g2
            simp at g2
            exact g2
        .
            -- Case: f(1) = -1, which implies f(x) = -x² for all x
            right
            right
            intro x
            specialize g2 x 1
            rw [g1] at g2
            simp at g2
            exact g2
    .
        -- Reverse direction: proving that each of the three specified functions
        -- satisfies the functional equation
        intro h
        simp at h
        rcases h with h | h | h
        all_goals
            simp [h]
        all_goals
            intro x y
            linarith
