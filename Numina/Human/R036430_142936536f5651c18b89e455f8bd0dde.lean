import Mathlib
/- Trouver tous les quadruplets de réels $(a, b, c, d)$ tels que

$$
a=b c+c d, b=c d+d a, c=d a+a b \text { et } d=a b+b c
$$ -/
theorem algebra_605458 (a b c d : ℝ) : a = b * c + c * d ∧ b = c * d + d * a ∧ c = d * a + a * b ∧ d = a * b + b * c ↔
(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 1 / 2 ∧ d = 1 / 2) := by
    constructor
    -- Forward direction: proving that any solution must be one of the two cases
    .
        intro h
        rcases h with ⟨h1, h2, h3, h4⟩
        -- Case analysis: either one of a,b,c,d is zero, or none are zero
        by_cases hze : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0
        -- Case 1: When one variable is zero, prove all variables must be zero
        .
            rcases hze with hze | hze | hze | hze
            -- Subcase: a = 0
            .
                rw [hze] at h3
                simp at h3
                rw [hze, h3] at h2 h4
                simp at h2 h4
                left
                refine ⟨?_, ?_, ?_, ?_⟩
                all_goals
                linarith
            -- Subcase: b = 0
            .
                rw [hze] at h4
                simp at h4
                rw [hze, h4] at h1 h3
                simp at h1 h3
                left
                refine ⟨?_, ?_, ?_, ?_⟩
                all_goals
                linarith
            -- Subcase: c = 0
            .
                rw [hze] at h1
                simp at h1
                rw [hze, h1] at h2 h4
                simp at h2 h4
                left
                refine ⟨?_, ?_, ?_, ?_⟩
                all_goals
                linarith
            -- Subcase: d = 0
            .
                rw [hze] at h2
                simp at h2
                rw [hze, h2] at h1 h3
                simp at h1 h3
                left
                refine ⟨?_, ?_, ?_, ?_⟩
                all_goals
                linarith
        -- Case 2: When no variable is zero, prove all variables must be 1/2
        .
            simp at hze
            right
            -- Key algebraic manipulations to show all variables equal 1/2
            have h5 : a * c = (b * c + c * d) * (d * a + a * b):= by rw [←h1, ←h3]
            replace h5 : a * c * ((b + d) ^ 2 - 1) = 0:= by linarith
            rcases hze with ⟨hze1, hze2, hze3, hze4⟩
            have g1 : a * c ≠ 0:= by positivity
            replace h5 : (b + d) ^ 2 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g1 h5
            have h6 : b * d = (c * d + d * a) * (a * b + b * c):= by rw [←h2, ←h4]
            replace h6 : (b * d) * ((a + c) ^ 2 - 1) = 0:= by linarith
            have g2 : b * d ≠ 0:= by positivity
            replace h6 : (a + c) ^ 2 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g2 h6
            have h7 : (a + c) * (b + d - 1) = 0:= by linarith
            have h8 : (b + d) * (a + c - 1) = 0:= by linarith
            have g3 : a + c ≠ 0:= by
                by_contra H
                rw [H] at h6
                simp at h6
            have g4 : b + d ≠ 0:= by
                by_contra H
                rw [H] at h5
                simp at h5
            replace h7 : b + d - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g3 h7
            replace h8 : a + c - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g4 h8
            replace h7 : b + d = 1:= by linarith
            replace h8 : a + c = 1:= by linarith
            clear h5 h6 g1 g2 g3 g4
            replace h1 : a = c * (b + d):= by linarith
            replace h2 : b = d * (a + c):= by linarith
            rw [h7] at h1
            rw [h8] at h2
            simp at h1 h2
            refine ⟨?_, ?_, ?_, ?_⟩
            all_goals
            linarith
    -- Backward direction: proving that both cases satisfy the system of equations
    .
        intro h
        rcases h with h | h
        -- Case: all variables are zero
        .
            rcases h with ⟨h1, h2, h3, h4⟩
            subst a b c d
            simp
        -- Case: all variables are 1/2
        .
            rcases h with ⟨h1, h2, h3, h4⟩
            subst a b c d
            refine ⟨?_, ?_, ?_, ?_⟩
            all_goals
            linarith
