import Mathlib
/- Find all integer solutions to: $a+b+c=24, a^{2}+b^{2}+c^{2}=210, a b c=440$. -/
theorem algebra_604698 : {(a, b, c) : ℤ × ℤ × ℤ| a + b + c = 24 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 210 ∧ a * b * c = 440} = {(5, 8, 11), (8, 5, 11), (5, 11, 8), (11, 5, 8), (8, 11, 5), (11, 8, 5)}:= by
    -- Extend to work with arbitrary triple (a,b,c)
    ext ⟨a, b, c⟩
    constructor
    .
        -- Forward direction: prove any solution must be one of the six permutations
        intro h
        simp at h
        rcases h with ⟨h1, h2, h3⟩
        -- Key insight: construct a polynomial that's equal for both sides
        have h4 : ∀ x : ℤ, (x - a) * (x - b) * (x - c) = (x - 5) * (x - 8) * (x - 11):= by
            intro x
            -- Prove that ab + bc + ca = 183 using the given conditions
            replace h2 : a * b + b * c + c * a = 183:= by
                have h5 : 2 * (a * b + b * c + c * a) = (a + b + c) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2):= by ring_nf
                rw [h1, h2] at h5
                ring_nf at h5
                rify at h5
                rify
                linarith
            -- Show polynomials are equal by expanding and using given conditions
            rw [show (x - a) * (x - b) * (x - c) = x ^ 3 - (a + b + c) * x ^ 2 + (a * b + b * c + c * a) * x - a * b * c by ring_nf]
            rw [h1, h2, h3]
            ring_nf
        -- Apply polynomial equality to each variable
        have h5:= h4 b
        have h6:= h4 c
        replace h4:= h4 a
        simp at h4 h5 h6
        -- Helper lemma to convert equations to actual values
        have g1 : ∀ a : ℤ, (a - 5 = 0 ∨ a - 8 = 0) ∨ a - 11 = 0 → a = 5 ∨ a = 8 ∨ a = 11:= by
            intro a h4
            rcases h4 with h4 | h4
            .
                rcases h4 with h4 | h4
                .
                    left
                    linarith
                .
                    right
                    left
                    linarith
            .
                right
                right
                linarith
        -- Apply helper lemma to each variable
        replace h4:= g1 a h4
        replace h5:= g1 b h5
        replace h6:= g1 c h6
        -- Case analysis on all possible combinations
        rcases h4 with h4 | h4 | h4
        all_goals
            rcases h5 with h5 | h5 | h5
            all_goals
                rcases h6 with h6 | h6 | h6
                any_goals
                    subst a b c
                    simp
                all_goals
                    norm_num at h1 h2 h3
    .
        -- Reverse direction: prove each of the six permutations satisfies the conditions
        intro h
        simp at h
        rcases h with h | h | h | h | h | h
        all_goals
        rcases h with ⟨h1, h2, h3⟩
        subst a b c
        simp
