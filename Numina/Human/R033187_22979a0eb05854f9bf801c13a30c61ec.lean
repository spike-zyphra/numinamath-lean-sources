import Mathlib
/- Find all real solutions to: $\mathrm{x}+\mathrm{y}-\mathrm{z}=-1 ; \mathrm{x}^{2}-\mathrm{y}^{2}+\mathrm{z}^{2}=1,-\mathrm{x}^{3}+\mathrm{y}^{3}+\mathrm{z}^{3}=-1$. -/

theorem algebra_604272 : {(x, y, z) : ℝ × ℝ × ℝ | x + y - z = -1 ∧ x ^ 2 - y ^ 2 + z ^ 2 = 1 ∧ -x ^ 3 + y ^ 3 + z ^ 3 = -1} = {(1, -1, 1), (-1, -1, -1)}:= by
    -- Use extensionality to prove equality of sets
    ext ⟨x, y, z⟩
    constructor
    .
        -- Forward direction: prove any solution is one of the two points
        intro h
        simp at h
        rcases h with ⟨h1, h2, h3⟩
        -- From first equation: express x in terms of y and z
        replace h1 : x = z - y - 1:= by linarith
        rw [h1] at h2
        -- Simplify second equation to get a product equal to zero
        replace h2 : (z - 1) * (z - y) = 0:= by linarith
        simp at h2
        rcases h2 with h2 | h2
        .
            -- Case 1: z = 1
            replace h2 : z = 1:= by linarith
            subst z
            simp at h1 h3
            rw [h1] at h3
            ring_nf at h3
            -- Factoring the cubic equation
            replace h3 : (y + 1) * (y ^ 2 + 1 + (y - 1) ^ 2) = 0:= by linarith
            -- Second factor is always positive
            have g1 : y ^ 2 + 1 + (y - 1) ^ 2 ≠ 0:= by positivity
            simp [g1] at h3
            replace h3 : y = -1:= by linarith
            subst y
            simp at h1
            subst x
            simp
        .
            -- Case 2: z = y
            replace h2 : z = y:= by linarith
            subst z
            simp at h1
            subst x
            ring_nf at h3
            -- Similar factoring as in Case 1
            replace h3 : (y + 1) * (y ^ 2 + 1 + (y - 1) ^ 2) = 0:= by linarith
            have g1 : y ^ 2 + 1 + (y - 1) ^ 2 ≠ 0:= by positivity
            simp [g1] at h3
            replace h3 : y = -1:= by linarith
            subst y
            simp
    .
        -- Backward direction: verify that both points satisfy the system
        intro h
        simp at h
        rcases h with h | h
        all_goals
            rcases h with ⟨h1, h2, h3⟩
            subst x y z
            simp
            ring_nf
