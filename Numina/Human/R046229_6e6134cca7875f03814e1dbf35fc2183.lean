import Mathlib
/- Determine the least positive value taken by the expression $a^{3}+b^{3}+c^{3}-3 a b c$ as $a, b, c$ vary over all positive integers. Find also all triples $(a, b, c)$ for which this least value is attained. -/
theorem algebra_607798 : (IsLeast {x : ℤ | ∃ a b c : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ∧ a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c > 0} 4)
 ∧ {(a, b, c) : ℤ × ℤ × ℤ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = 4} = {(1 ,1 ,2), (1, 2, 1), (2, 1, 1)}:= by

    -- Split the proof into two parts: proving 4 is the minimum and finding all solutions
    constructor
    .
        simp
        constructor
        .
            -- Show that 4 is in the set by using the triple (1,1,2)
            simp
            use 1
            simp
            use 1
            simp
            use 2
            simp
        .
            -- Prove that 4 is indeed the minimum value
            simp [lowerBounds]
            intro x a ha b hb c hc hx h
            subst x

            -- Key inequality: (a+b+c)*((a-b)²+(b-c)²+(c-a)²) ≥ 8
            suffices (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥ 4 * 2 by linarith
            replace h : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) > 0:= by linarith

            -- Prove that (a-b)²+(b-c)²+(c-a)² > 0
            have h1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 > 0:= by
                by_contra H
                simp at H
                have H1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0:= by positivity
                replace H : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0:= by linarith
                rw [H] at h
                simp at h

            -- Prove that (a-b)²+(b-c)²+(c-a)² ≥ 2
            replace h1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 2:= by
                by_contra H
                simp at H
                replace H : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 1:= by linarith
                by_cases hab : a = b
                .
                    subst a
                    simp at H
                    replace H : 2 * (b - c) ^ 2 = 1:= by linarith
                    replace H : 1 % 2 = 0:= by omega
                    simp at H
                .
                    replace hab : a - b ≠ 0:= by
                        by_contra H1
                        replace H1 : a = b:= by linarith
                        trivial
                    replace hab : (a - b) ^ 2 > 0:= by positivity
                    have g1 : (b - c) ^ 2 ≥ 0:= by positivity
                    have g2 : (c - a) ^ 2 ≥ 0:= by positivity
                    replace g1 : (b - c) ^ 2 = 0:= by linarith
                    replace g2 : (c - a) ^ 2 = 0:= by linarith
                    simp at g1 g2
                    replace g1 : b = c:= by linarith
                    replace g2 : c = a:= by linarith
                    subst b c
                    simp at hab

            -- Prove that a+b+c ≥ 4
            have h2 : a + b + c ≥ 4:= by
                by_contra H
                simp at H
                replace ha : a = 1:= by linarith
                replace hb : b = 1:= by linarith
                replace hc : c = 1:= by linarith
                subst a b c
                simp at h1
            refine Int.mul_le_mul h2 h1 (by linarith) (by linarith)
    .
        -- Prove that the only solutions are (1,1,2), (1,2,1), and (2,1,1)
        ext ⟨a, b, c⟩
        constructor
        .
            intro h
            simp at h
            rcases h with ⟨ha, hb, hc, h⟩
            replace h : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) = 8:= by linarith

            -- Prove that 4 ≤ a+b+c ≤ 4, thus a+b+c = 4
            have h1 : a + b + c ≥ 4:= by
                by_contra H
                simp at H
                replace ha : a = 1:= by linarith
                replace hb : b = 1:= by linarith
                replace hc : c = 1:= by linarith
                subst a b c
                simp at h
            have h2 : a + b + c ≤ 4:= by
                by_contra H
                simp at H
                have h2 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 2:= by
                    by_contra H1
                    simp at H1
                    by_cases hab : a = b
                    .
                        subst a
                        simp at H1
                        have g1 : (b - c) ^ 2 ≥ 0:= by positivity
                        replace g1 : (b - c) ^ 2 = 0:= by linarith
                        simp at g1
                        replace g1 : b = c:= by linarith
                        subst b
                        linarith
                    .
                        replace hab : a - b ≠ 0:= by
                            by_contra H1
                            replace H1 : a = b:= by linarith
                            trivial
                        replace hab : (a - b) ^ 2 > 0:= by positivity
                        have g1 : (b - c) ^ 2 ≥ 0:= by positivity
                        have g2 : (c - a) ^ 2 ≥ 0:= by positivity
                        replace g1 : (b - c) ^ 2 = 0:= by linarith
                        replace g2 : (c - a) ^ 2 = 0:= by linarith
                        simp at g1 g2
                        replace g1 : b = c:= by linarith
                        replace g2 : c = a:= by linarith
                        subst b c
                        simp at hab
                replace H : a + b + c ≥ 5:= by linarith
                replace H : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥ 5 * 2:= by refine Int.mul_le_mul H h2 (by linarith) (by linarith)
                linarith

            -- Given a+b+c = 4 and all variables positive, enumerate all possibilities
            replace h2 : a + b + c = 4:= by linarith
            have ha1 : a ≤ 2:= by linarith
            have hb1 : b ≤ 2:= by linarith
            have hc1 : c ≤ 2:= by linarith
            replace ha1 : a = 1 ∨ a = 2:= by omega
            rcases ha1 with ha1 | ha1
            .
                subst a
                replace hb1 : b = 1 ∨ b = 2:= by omega
                rcases hb1 with hb1 | hb1
                .
                    subst b
                    replace h2 : c = 2:= by linarith
                    subst c
                    simp
                .
                    subst b
                    replace h2 : c = 1:= by linarith
                    subst c
                    simp
            .
                subst a
                replace h1 : b = 1:= by linarith
                replace h2 : c = 1:= by linarith
                subst b c
                simp
        .
            -- Verify that each of the three solutions satisfies the conditions
            intro h
            simp at h
            rcases h with h | h | h
            all_goals
                rcases h with ⟨ha, hb, hc⟩
                subst a b c
                simp
