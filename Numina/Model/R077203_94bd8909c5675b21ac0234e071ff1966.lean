import Mathlib

/- Given real numbers ${{x}_{1}},{{x}_{2}},{{x}_{3}}$ satisfy $x_{1}^{2}+x_{2}^{2}+x_{3}^{2}+{{x}_{1}}{{x}_{2}}+{{x}_{2}}{{x}_{3}}=2$, then the maximum value of $\left| {{x}_{2}} \right|$ is ___          ___. -/
theorem algebra_12215 (x1 x2 x3 : ℝ) (h : x1^2 + x2^2 + x3^2 + x1 * x2 + x2 * x3 = 2) :
    |x2| ≤ 2 := by
  have h1 : (x1 + x2 / 2)^2 + (x3 + x2 / 2)^2 ≥ 0 := by
    apply add_nonneg
    · apply sq_nonneg
    · apply sq_nonneg
  -- Now, we use nlinarith to solve the inequality
  have h2 : x2 ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (x1 + x2 / 2), sq_nonneg (x3 + x2 / 2)]
  have h3 : -2 ≤ x2 := by nlinarith [sq_nonneg x2]
  have h4 : x2 ≤ 2 := by nlinarith [sq_nonneg x2]
  apply abs_le.mpr
  constructor <;> linarith