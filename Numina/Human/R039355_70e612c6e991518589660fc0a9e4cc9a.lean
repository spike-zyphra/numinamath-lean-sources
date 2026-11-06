import Mathlib
/- Déterminer tous les nombres réels $x, y, z$ satisfaisant le système d'équations suivant : $x=\sqrt{2 y+3}, y=\sqrt{2 z+3}, z=\sqrt{2 x+3}$. -/
theorem algebra_604875 (x y z : ℝ) : (x = √(2 * y + 3) ∧ y = √(2 * z + 3) ∧ z = √(2 * x + 3)) ↔ x = 3 ∧ y = 3 ∧ z = 3 := by
    constructor

    -- Forward direction: proving that if the equations hold, then x = y = z = 3
    .
        intro h
        -- Split the hypothesis into three parts
        rcases h with ⟨h1, h2, h3⟩

        -- Since x is a square root, x ≥ 0
        have g1 : x ≥ 0:= by rw [h1] ; positivity
        -- Since y is a square root, y ≥ 0
        have g2 : y ≥ 0:= by rw [h2] ; positivity
        -- Since z is a square root, z ≥ 0
        have g3 : z ≥ 0:= by rw [h3] ; positivity

        -- Square both sides of each equation to eliminate square roots
        replace h1 : x ^ 2 = √(2 * y + 3) ^ 2:= by rw [h1]
        rw [show √(2 * y + 3) ^ 2 = 2 * y + 3 by refine Real.sq_sqrt (by linarith)] at h1
        replace h2 : y ^ 2 = √(2 * z + 3) ^ 2:= by rw [h2]
        rw [show √(2 * z + 3) ^ 2 = 2 * z + 3 by refine Real.sq_sqrt (by linarith)] at h2
        replace h3 : z ^ 2 = √(2 * x + 3) ^ 2:= by rw [h3]
        rw [show √(2 * x + 3) ^ 2 = 2 * x + 3 by refine Real.sq_sqrt (by linarith)] at h3

        -- Case analysis: either x ≥ y or x < y
        by_cases hx : x ≥ y

        -- Case 1: x ≥ y
        .
            -- From the equations, we can deduce z² ≥ x²
            have h4 : z ^ 2 ≥ x ^ 2:= by linarith
            -- If z² ≥ x², then |z| ≥ |x|
            replace h4 : |z| ≥ |x|:= by exact sq_le_sq.mp h4
            -- Since z ≥ 0, |z| = z
            rw [abs_of_nonneg (by linarith)] at h4
            -- Since x ≥ 0, |x| = x
            rw [abs_of_nonneg (by linarith)] at h4

            -- Similarly, y² ≥ z²
            have h5 : y ^ 2 ≥ z ^ 2:= by linarith
            -- Therefore |y| ≥ |z|
            replace h5 : |y| ≥ |z|:= by exact sq_le_sq.mp h5
            -- Since y ≥ 0, |y| = y
            rw [abs_of_nonneg (by linarith)] at h5
            -- Since z ≥ 0, |z| = z
            rw [abs_of_nonneg (by linarith)] at h5

            -- From the inequalities, we can deduce x = y
            replace hx : x = y:= by linarith
            -- Substitute x for y in h1
            rw [←hx] at h1
            -- Simplify to get quadratic equation
            replace h1 : (x + 1) * (x - 3) = 0:= by linarith

            -- Prove x + 1 ≠ 0 since x ≥ 0
            have h6 : x + 1 ≠ 0:= by
                by_contra H
                linarith
            -- Therefore x = 3
            replace h1 : x - 3 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h6 h1
            -- Prove all three equations
            refine ⟨?_, ?_, ?_⟩
            all_goals
            linarith

        -- Case 2: x < y
        .
            simp at hx
            -- From equations, z² < x²
            have h4 : z ^ 2 < x ^ 2:= by linarith
            -- Therefore |z| < |x|
            replace h4 : |z| < |x|:= by exact sq_lt_sq.mp h4
            -- Since z ≥ 0, |z| = z
            rw [abs_of_nonneg (by linarith)] at h4
            -- Since x ≥ 0, |x| = x
            rw [abs_of_nonneg (by linarith)] at h4
            -- From equations, y² < z²
            have h5 : y ^ 2 < z ^ 2:= by linarith
            -- Therefore |y| < |z|
            replace h5 : |y| < |z|:= by exact sq_lt_sq.mp h5
            -- Since y ≥ 0, |y| = y
            rw [abs_of_nonneg (by linarith)] at h5
            -- Since z ≥ 0, |z| = z
            rw [abs_of_nonneg (by linarith)] at h5
            by_contra _
            linarith

    -- Backward direction: proving that if x = y = z = 3, then the equations hold
    .
        intro h
        rcases h with ⟨h1, h2, h3⟩
        subst x y z
        simp
        ring_nf
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
        refine Eq.symm (Real.sqrt_sq (by linarith))
