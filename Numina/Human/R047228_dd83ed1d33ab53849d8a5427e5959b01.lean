import Mathlib

/- Given real numbers $a, b$ and $c$ such that $0 \leqslant a, b, c \leqslant 2$, prove that

$$
(a-b)(b-c)(a-c) \leqslant 2
$$ -/
theorem algebra_607143 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2) (hc : 0 ≤ c ∧ c ≤ 2) : (a - b) * (b - c) * (a - c) ≤ 2 := by
    -- First, consider the case where the product is negative
    by_cases h : (a - b) * (b - c) * (a - c) < 0
    .
        linarith
    .
        -- For the case where the product is non-negative
        simp at h
        -- Unpack the bounds for a, b, and c
        rcases ha with ⟨ha1, ha2⟩
        rcases hb with ⟨hb1, hb2⟩
        rcases hc with ⟨hc1, hc2⟩
        -- Prove that at least one of b ≥ a, c ≥ b, or a ≥ c must be true
        -- (otherwise we'd have a > b > c > a, which is impossible)
        have h1 : b ≥ a ∨ c ≥ b ∨ a ≥ c := by
            by_contra H
            simp at H
            rcases H with ⟨H1, H2, H3⟩
            replace H1 : a - b > 0 := by linarith
            replace H2 : b - c > 0 := by linarith
            replace H3 : c - a > 0 := by linarith
            have _ : (a - b) * (b - c) * (c - a) > 0 := by positivity
            linarith
        -- Handle each case separately
        rcases h1 with h1 | h1 | h1
        .
            -- Case 1: b ≥ a
            -- Rearrange the expression
            rw [show (a - b) * (b - c) * (a - c) = (b - c) * (c - a) * (b - a) by ring]
            -- Use the inequality (b-c)(c-a) ≤ (b-a)²/4
            have h2 : (b - c) * (c - a) ≤ (b - a) ^ 2 / 4:= by
                have h2 : (b + a - 2 * c) ^ 2 ≥ 0 := by positivity
                linarith
            replace h1 : b - a ≥ 0:= by linarith
            replace h2 : (b - c) * (c - a) * (b - a) ≤ (b - a) ^ 2 / 4 * (b - a) := by exact mul_le_mul_of_nonneg_right h2 h1
            suffices (b - a) ^ 3 ≤ 2 ^ 3 by linarith
            have h3 : b - a ≤ 2 := by linarith
            exact pow_le_pow_left h1 h3 3
        .
            -- Case 2: c ≥ b
            -- Similar approach with different rearrangement
            rw [show (a - b) * (b - c) * (a - c) = (a - b) * (c - a) * (c - b) by ring]
            have h2 : (a - b) * (c - a) ≤ (c - b) ^ 2 / 4:= by
                have h2 : (b + c - 2 * a) ^ 2 ≥ 0 := by positivity
                linarith
            replace h1 : c - b ≥ 0:= by linarith
            replace h2 : (a - b) * (c - a) * (c - b) ≤ (c - b) ^ 2 / 4 * (c - b) := by exact mul_le_mul_of_nonneg_right h2 h1
            suffices (c - b) ^ 3 ≤ 2 ^ 3 by linarith
            have h3 : c - b ≤ 2 := by linarith
            exact pow_le_pow_left h1 h3 3
        .
            -- Case 3: a ≥ c
            -- Use the inequality (a-b)(b-c) ≤ (a-c)²/4
            have h2 : (a - b) * (b - c) ≤ (a - c) ^ 2 / 4:= by
                have h2 : (a + c - 2 * b) ^ 2 ≥ 0 := by positivity
                linarith
            replace h1 : a - c ≥ 0:= by linarith
            replace h2 : (a - b) * (b - c) * (a - c) ≤ (a - c) ^ 2 / 4 * (a - c) := by exact mul_le_mul_of_nonneg_right h2 h1
            suffices (a - c) ^ 3 ≤ 2 ^ 3 by linarith
            have h3 : a - c ≤ 2 := by linarith
            exact pow_le_pow_left h1 h3 3
