import Mathlib
/- Let $a, b$ and $c$ be positive real numbers such that $a+b+c=1$. Prove that

$$
\frac{a}{b}+\frac{b}{a}+\frac{b}{c}+\frac{c}{b}+\frac{c}{a}+\frac{a}{c}+6 \geq 2 \sqrt{2}\left(\sqrt{\frac{1-a}{a}}+\sqrt{\frac{1-b}{b}}+\sqrt{\frac{1-c}{c}}\right)
$$

When does equality hold? -/

theorem algebra_605377 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) :
a / b + b / a + b / c + c / b + c / a + a / c + 6 ≥ 2 * √2 * (√((1 - a) / a) + √((1 - b) / b) + √((1 - c) / c)) ∧ (a / b + b / a + b / c + c / b + c / a + a / c + 6 = 2 * √2 * (√((1 - a) / a) + √((1 - b) / b) + √((1 - c) / c)) ↔ a = 1 / 3 ∧ b = 1 / 3 ∧ c = 1 / 3):= by

    -- Rewrite 1-a, 1-b, 1-c using the condition a+b+c=1
    rw [show 1 - a = b + c by linarith]
    rw [show 1 - b = c + a by linarith]
    rw [show 1 - c = a + b by linarith]

    -- Simplify the left side of the inequality using ring arithmetic
    rw [show a / b + b / a + b / c + c / b + c / a + a / c = (b + c) / a + (c + a) / b + (a + b) / c by ring]

    -- Express the sum in terms of squares of square roots plus a constant
    have h1 : (b + c) / a + (c + a) / b + (a + b) / c + 6 = √((b + c) / a) ^ 2 + √((c + a) / b) ^ 2 + √((a + b) / c) ^ 2 + 3 * √2 ^ 2:= by
        rw [Real.sq_sqrt (by positivity)]
        rw [Real.sq_sqrt (by positivity)]
        rw [Real.sq_sqrt (by positivity)]
        rw [Real.sq_sqrt (by positivity)]
        linarith
    rw [h1]

    -- Key inequality: sum of squares of differences is non-negative
    have h2 : (√((b + c) / a) - √2) ^ 2 + (√((c + a) / b) - √2) ^ 2 + (√((a + b) / c) - √2) ^ 2 ≥ 0:= by positivity
    constructor
    .
        linarith
    .
        constructor
        .
            -- Forward direction: if equality holds, then a=b=c=1/3
            intro hgoal
            -- Show each squared term must be zero
            have g1 : (√((b + c) / a) - √2) ^ 2 ≥ 0:= by positivity
            have g2 : (√((c + a) / b) - √2) ^ 2 ≥ 0:= by positivity
            have g3 : (√((a + b) / c) - √2) ^ 2 ≥ 0:= by positivity
            replace g1 : (√((b + c) / a) - √2) ^ 2 = 0:= by linarith
            replace g2 : (√((c + a) / b) - √2) ^ 2 = 0:= by linarith
            replace g3 : (√((a + b) / c) - √2) ^ 2 = 0:= by linarith

            -- Extract the square root terms
            replace g1 : √((b + c) / a) - √2 = 0:= by exact pow_eq_zero g1
            replace g2 : √((c + a) / b) - √2 = 0:= by exact pow_eq_zero g2
            replace g3 : √((a + b) / c) - √2 = 0:= by exact pow_eq_zero g3
            replace g1 : √((b + c) / a) = √2:= by linarith
            replace g2 : √((c + a) / b) = √2:= by linarith
            replace g3 : √((a + b) / c) = √2:= by linarith

            -- Square both sides
            replace g1 : √((b + c) / a) ^ 2 = √2 ^ 2:= by rw [g1]
            replace g2 : √((c + a) / b) ^ 2 = √2 ^ 2:= by rw [g2]
            replace g3 : √((a + b) / c) ^ 2 = √2 ^ 2:= by rw [g3]
            rw [Real.sq_sqrt (by positivity)] at g1 g2 g3
            rw [Real.sq_sqrt (by positivity)] at g1 g2 g3
            field_simp at g1 g2 g3
            refine ⟨?_, ?_, ?_⟩
            all_goals
            linarith
        .
            -- Backward direction: if a=b=c=1/3, then equality holds
            intro hgoal
            rcases hgoal with ⟨ga, gb, gc⟩
            subst a b c
            ring_nf
