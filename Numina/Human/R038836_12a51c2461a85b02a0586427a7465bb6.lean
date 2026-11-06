import Mathlib
/- Let $a, b$, and $c$ be non-negative real numbers, no two of which are equal. Prove that

$$
\frac{a^{2}}{(b-c)^{2}}+\frac{b^{2}}{(c-a)^{2}}+\frac{c^{2}}{(a-b)^{2}}>2
$$ -/
theorem algebra_605866 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hne : ¬(a = b) ∧ ¬(b = c) ∧ ¬(a = c)) :
    2 < a ^ 2 / (b - c) ^ 2 + b ^ 2 / (c - a) ^ 2 + c ^ 2 / (a - b) ^ 2 := by
        -- First prove the inequality for the case when a > b > c
        have h1 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a > b → b > c → a ^ 2 / (b - c) ^ 2 + b ^ 2 / (c - a) ^ 2 + c ^ 2 / (a - b) ^ 2 > 2:= by
            intro a b c _ _ hc h1 h2
            -- Prove that a² ≥ (a-c)² using non-negativity of c
            have h3 : a ^ 2 ≥ (a - c) ^ 2:= by
                have g1 : 2 * a - c ≥ 0:= by linarith
                replace g1 : c * (2 * a - c) ≥ 0:= by positivity
                linarith
            -- Similarly prove that b² ≥ (b-c)²
            have h4 : b ^ 2 ≥ (b - c) ^ 2:= by
                have g1 : 2 * b - c ≥ 0:= by linarith
                replace g1 : c * (2 * b - c) ≥ 0:= by positivity
                linarith
            -- The third term is non-negative
            have h5 : c ^ 2 / (a - b) ^ 2 ≥ 0:= by positivity
            -- Apply division inequality for the first term
            replace h3 : a ^ 2 / (b - c) ^ 2 ≥ (a - c) ^ 2 / (b - c) ^ 2:= by exact div_le_div_of_nonneg_right h3 (by positivity)
            -- Apply division inequality for the second term
            replace h4 : b ^ 2 / (c - a) ^ 2 ≥ (b - c) ^ 2 / (c - a) ^ 2:= by exact div_le_div_of_nonneg_right h4 (by positivity)
            -- Reduce to proving inequality without the third term
            suffices (a - c) ^ 2 / (b - c) ^ 2 + (b - c) ^ 2 / (c - a) ^ 2 - 2 * 1 > 0 by linarith
            clear h3 h4 h5
            -- Establish positivity of denominators
            have h3 : b - c > 0:= by linarith
            have h4 : a - c > 0:= by linarith
            -- Series of algebraic manipulations to simplify the expression
            rw [show (c - a) ^ 2 = (a - c) ^ 2 by ring]
            rw [show 1 = (a - c) / (b - c) * ((b - c) / (a - c)) by field_simp]
            rw [show (a - c) ^ 2 / (b - c) ^ 2 = ((a - c) / (b - c)) ^ 2 by field_simp]
            rw [show (b - c) ^ 2 / (a - c) ^ 2 = ((b - c) / (a - c)) ^ 2 by field_simp]
            -- Prove that the difference of fractions is non-zero
            have h5 : ((a - c) / (b - c) - (b - c) / (a - c)) ^ 2 > 0:= by
                have h5 : (a - c) / (b - c) - (b - c) / (a - c) ≠ 0:= by
                    by_contra H
                    field_simp at H
                    replace H : (a - b) * (a + b - 2 * c) = 0:= by linarith
                    replace H : a - b = 0 ∨ a + b - 2 * c = 0:= by exact mul_eq_zero.mp H
                    rcases H with H | H
                    all_goals
                    linarith
                positivity
            linarith

        -- Handle all possible orderings of a, b, c using the previous result
        rcases hne with ⟨ga, gb, gc⟩
        -- Split into cases based on relative ordering
        replace ga : a < b ∨ a > b:= by exact lt_or_gt_of_ne ga
        replace gb : b < c ∨ b > c:= by exact lt_or_gt_of_ne gb
        replace gc : a < c ∨ a > c:= by exact lt_or_gt_of_ne gc
        -- Case analysis for all possible orderings
        rcases ga with ga | ga
        .
            rcases gb with gb | gb
            .
                specialize h1 c b a hc hb ha gb ga
                rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring]
                rw [show (c - a) ^ 2 = (a - c) ^ 2 by ring]
                rw [show (b - c) ^ 2 = (c - b) ^ 2 by ring]
                linarith
            .
                rcases gc with gc | gc
                .
                    specialize h1 b c a hb hc ha gb gc
                    linarith
                .
                    specialize h1 b a c hb ha hc ga gc
                    rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring]
                    rw [show (c - a) ^ 2 = (a - c) ^ 2 by ring]
                    rw [show (b - c) ^ 2 = (c - b) ^ 2 by ring]
                    linarith
        .
            rcases gb with gb | gb
            .
                rcases gc with gc | gc
                .
                    specialize h1 c a b hc ha hb gc ga
                    linarith
                .
                    specialize h1 a c b ha hc hb gc gb
                    rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring]
                    rw [show (c - a) ^ 2 = (a - c) ^ 2 by ring]
                    rw [show (b - c) ^ 2 = (c - b) ^ 2 by ring]
                    linarith
            .
                specialize h1 a b c ha hb hc ga gb
                exact h1
