import Mathlib
/- 82. Given $x, y>0$, and $x^{3}+y^{4} \leqslant x^{2}+y^{3}$, prove: $x^{3}+y^{3} \leqslant 2$. (2002 Hungarian Mathematical Olympiad problem) -/
theorem inequalities_600696 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^4 ≤ x^2 + y^3) : x^3 + y^3 ≤ 2 := by
  -- Using the nlinarith tactic to solve the inequality
  -- We provide several non-negative expressions as hints:
  -- (x-1)², (y-1)², (x²-1)², (y²-1)², (x-y)², (x²-y²)², (x³-1)², (y³-1)²
  -- along with our hypothesis h: x^3 + y^4 ≤ x^2 + y^3
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1),
    sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (x - y), sq_nonneg (x^2 - y^2),
    sq_nonneg (x^3 - 1), sq_nonneg (y^3 - 1), h]
