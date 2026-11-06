import Mathlib
/- If $a, b, c, x$ are real numbers such that $a b c \neq 0$ and

$$
\frac{x b+(1-x) c}{a}=\frac{x c+(1-x) a}{b}=\frac{x a+(1-x) b}{c}
$$

then prove that either $a+b+c=0$ or $a=b=c$. -/

theorem algebra_607787 {a b c x : ℝ} (h : a * b * c ≠ 0) (h1 : (x * b + (1 - x) * c) / a = (x * c + (1 - x) * a) / b)
(h2 : (x * c + (1 - x) * a) / b = (x * a + (1 - x) * b) / c) : a + b + c = 0 ∨ a = b ∧ b = c:= by

    -- Case split on whether a+b+c=0
    by_cases habc : a + b + c = 0
    .
        -- If a+b+c=0, we're done with the left part of the disjunction
        left
        exact habc
    .
        -- If a+b+c≠0, prove a=b=c
        right
        -- Let t be the common value of the fractions
        set t:= (x * b + (1 - x) * c) / a with h3
        clear_value t
        rw [←h1] at h2

        -- Break down the non-zero conditions
        replace h : a * b ≠ 0 ∧ c ≠ 0:= by exact mul_ne_zero_iff.mp h
        rcases h with ⟨ha, hc⟩
        replace ha : a ≠ 0 ∧ b ≠ 0:= by exact mul_ne_zero_iff.mp ha
        rcases ha with ⟨ha, hb⟩

        -- Simplify field expressions and prove t=1
        field_simp at h1 h2 h3
        have h4 : (a + b + c) * (t - 1) = 0:= by linarith
        replace h4 : t - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero habc h4
        replace h4 : t = 1:= by linarith
        subst t
        simp at h1 h2 h3

        -- Prove x²-x+1>0 for all x
        have g1 : x ^ 2 - x + 1 ≠ 0:= by
            have g1 : x ^ 2 - x + 1 > 0:= by
                have g1 : (x - 1 / 2) ^ 2 + 3 / 4 > 0:= by positivity
                linarith
            positivity

        -- Use the quadratic to prove a=b and b=c
        have h4 : (x ^ 2 - x + 1) * (a - b) = 0:= by
            rw [h2] at h1 h3
            linarith
        have h5 : (x ^ 2 - x + 1) * (b - c) = 0:= by
            rw [h1] at h2 h3
            linarith
        replace h4 : a - b = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g1 h4
        replace h5 : b - c = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g1 h5

        -- Conclude a=b and b=c
        constructor
        all_goals
        linarith
