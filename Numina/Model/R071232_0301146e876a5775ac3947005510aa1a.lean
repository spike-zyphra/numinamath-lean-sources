import Mathlib

/- If the real numbers $x$, $y$ satisfy ${{x}^{3}}+{{y}^{3}}+3xy=1$, then the minimum value of ${{x}^{2}}+{{y}^{2}}$ is ___          ___. -/
theorem algebra_297 :
    IsLeast {t : ℝ | ∃ x y, t = x ^ 2 + y ^ 2 ∧ x ^ 3 + y ^ 3 + 3 * x * y = 1} (1 / 2) := by
  constructor
  · -- Show \(1/2\) is achievable with \(x = y = 1/2\).
    use 1 / 2, 1 / 2
    norm_num
  · -- Show \(1/2\) is a lower bound.
    intro t ht
    rcases ht with ⟨x, y, h_eq, heq⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1 / 4), sq_nonneg (x + y - 1)]