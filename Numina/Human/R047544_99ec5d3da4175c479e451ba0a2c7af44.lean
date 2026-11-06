import Mathlib
/- 46. Given that $a, b$ are positive real numbers, and $a^{5}+b^{5}=a^{3}+b^{3}$, prove: $a^{2}+b^{2} \leqslant 1+a b$. (2003 Polish Mathematical Olympiad Problem) -/
theorem inequalities_599222 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^5 + b^5 = a^3 + b^3) :
    a^2 + b^2 ≤ 1 + a * b := by
        -- Using the nlinarith tactic to solve the inequality
        -- We provide several non-negative expressions as hints:
        -- (a^2 - b^2)^2 ≥ 0: square of difference of squares
        -- (a - b)^2 ≥ 0: square of difference
        -- (a^2 - 1)^2 ≥ 0: square of a^2 - 1
        -- (b^2 - 1)^2 ≥ 0: square of b^2 - 1
        -- We also include the main hypothesis h: a^5 + b^5 = a^3 + b^3
        -- mul_pos ha hb: a*b > 0 (product of positive numbers)
        -- (a - 1)^2 ≥ 0: square of a - 1
        -- (b - 1)^2 ≥ 0: square of b - 1
        -- (a^2 + b^2 - 1 - a*b)^2 ≥ 0: square of the expression we're trying to prove is ≤ 0
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1),
                  h, mul_pos ha hb, sq_nonneg (a - 1), sq_nonneg (b - 1),
                  sq_nonneg (a^2 + b^2 - 1 - a * b)]
