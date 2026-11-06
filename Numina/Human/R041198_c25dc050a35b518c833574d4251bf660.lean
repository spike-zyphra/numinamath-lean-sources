import Mathlib
set_option maxHeartbeats 400000000
/- 2. Solve the equation


$$

\sqrt{\frac{x-2}{11}}+\sqrt{\frac{x-3}{10}}=\sqrt{\frac{x-11}{2}}+\sqrt{\frac{x-10}{3}}

$$
 -/
theorem algebra_177177 (x : ℝ) (hx : x ≥ 11) :
    Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10) =
    Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3) ↔ x = 13 := by
        constructor
        --Assume Real.sqrt ((x - 2) / 11) + Real.sqrt ((x - 3) / 10) = Real.sqrt ((x - 11) / 2) + Real.sqrt ((x - 10) / 3)
        intro h
        --Put t = x - 13
        set t := x - 13

        --Obtain x = t + 13.
        have ht1 : x = t + 13 := by ring

        --Since x ≥ 11 we have t ≥ -2.
        have ht2 : t ≥ -2 := by linarith

        --Now either -2 ≤ t < 0 or 0 < t or t = 0.
        have htcond : (-2 ≤ t ∧ t < 0) ∨ (0 < t) ∨ (t = 0) := by
            have h_cases : t < 0 ∨ t = 0 ∨ t > 0 := by exact lt_trichotomy t 0
            rcases h_cases with ht | heq | ht
            left
            exact ⟨ht2, ht⟩
            right
            right
            exact heq
            right
            left
            exact ht

        --Now we show that t = 0 is the only possible case.

        --First, let's show -2 ≤ t ∧ t < 0 is impossible.
        have hcont1 : ¬ (-2 ≤ t ∧ t < 0) := by
            --Assume -2 ≤ t ∧ t < 0.
            by_contra h'
            --Show by back-substituting Real.sqrt (t / 11 + 1) + Real.sqrt (t / 10 + 1) = Real.sqrt (t / 2 + 1) + Real.sqrt (t / 3 + 1) as follows.
            have h1 : Real.sqrt (t / 11 + 1) + Real.sqrt (t / 10 + 1) = Real.sqrt (t / 2 + 1) + Real.sqrt (t / 3 + 1) := by
                have h11 : t / 11 + 1 = (x - 2) / 11 := by
                    linarith
                have h12 : t / 10 + 1 = (x - 3) / 10 := by
                    linarith
                have h13 : t / 2 + 1 = (x - 11) / 2 := by
                    linarith
                have h14 : t / 3 + 1 = (x - 10) / 3 := by
                    linarith
                rw [← h11, ← h12, ← h13, ← h14] at h
                exact h

            --Show Real.sqrt (t / 11 + 1) + Real.sqrt (t / 10 + 1) > Real.sqrt (t / 2 + 1) + Real.sqrt (t / 3 + 1)
            have h2 : Real.sqrt (t / 11 + 1) + Real.sqrt (t / 10 + 1) > Real.sqrt (t / 2 + 1) + Real.sqrt (t / 3 + 1) := by
                --First show t / 2 + 1 < t / 11 + 1
                have h21 : t / 2 + 1 < t / 11 + 1 := by
                    have : t < 0 := by exact h'.2
                    linarith
                refine add_lt_add ?_ ?_
                refine (Real.sqrt_lt_sqrt_iff_of_pos ?_).mpr h21
                linarith

                --Then show t / 3 + 1 < t / 10 + 1. Now taking square roots proves the inequality.
                have h22 : t / 3 + 1 < t / 10 + 1 := by
                    have : t ≥ -2 := by exact h'.1
                    linarith
                refine (Real.sqrt_lt_sqrt_iff_of_pos ?_).mpr h22
                linarith
            --Obtain 1 > 1 by linarith. This is a contradiction.
            have : 1 > 1 := by linarith
            contradiction

        --Second, let's show that it's not the case that 0 < t.
        have hcont2 : ¬ (0 < t) := by
            --Assume 0 < t
            by_contra h'
            --As before, show by back-substituting Real.sqrt (t / 11 + 1) + Real.sqrt (t / 10 + 1) = Real.sqrt (t / 2 + 1) + Real.sqrt (t / 3 + 1) as follows.
            have h1 : Real.sqrt (t / 11 + 1) + Real.sqrt (t / 10 + 1) = Real.sqrt (t / 2 + 1) + Real.sqrt (t / 3 + 1) := by
                    have h11 : t / 11 + 1 = (x - 2) / 11 := by
                        linarith
                    have h12 : t / 10 + 1 = (x - 3) / 10 := by
                        linarith
                    have h13 : t / 2 + 1 = (x - 11) / 2 := by
                        linarith
                    have h14 : t / 3 + 1 = (x - 10) / 3 := by
                        linarith
                    rw [← h11, ← h12, ← h13, ← h14] at h
                    exact h

            --Show Real.sqrt (t / 11 + 1) + Real.sqrt (t / 10 + 1) < Real.sqrt (t / 2 + 1) + Real.sqrt (t / 3 + 1)
            have h2 : Real.sqrt (t / 11 + 1) + Real.sqrt (t / 10 + 1) < Real.sqrt (t / 2 + 1) + Real.sqrt (t / 3 + 1) := by
                --First show t / 2 + 1 > t / 11 + 1
                    have h21 : t / 2 + 1 > t / 11 + 1 := by
                        have : t > 0 := by exact h'
                        linarith
                    refine add_lt_add ?_ ?_
                    refine (Real.sqrt_lt_sqrt_iff_of_pos ?_).mpr h21
                    linarith

                --Then show t / 3 + 1 > t / 10 + 1. Now taking square roots proves the inequality.
                    have h22 : t / 3 + 1 > t / 10 + 1 := by
                        have : t > 0 := by exact h'
                        linarith
                    refine (Real.sqrt_lt_sqrt_iff_of_pos ?_).mpr h22
                    linarith
                --Get the contradiction.
                    --Obtain 1 > 1 by linarith. This is a contradiction.
            have : 1 > 1 := by linarith
            contradiction

        --So the only possibility is t = 0.
        have ht0 : t = 0 := by tauto

        --`linarith` closes the goal
        linarith

        --Conversely assume x = 13.
        intro h
        --Substitute x = 13 in the goal.
        rw [h]
        norm_num
        --Done