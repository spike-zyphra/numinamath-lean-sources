import Mathlib

open Real Set

theorem algebra_180123 :
    IsGreatest {x | ∃ a b c d : ℝ, x = (a - b)^2 + (a - c)^2 + (a - d)^2 + (b - c)^2 + (b - d)^2 + (c - d)^2 ∧ a^2 + b^2 + c^2 + d^2 = 5} 20 := by
  constructor
  · -- $20$ can be attained using $\pm \sqrt{5}/2$.
    use Real.sqrt (5) / 2, Real.sqrt (5) / 2, -Real.sqrt (5) / 2, -Real.sqrt (5) / 2
    constructor
    · -- Verify it's equal to 20
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    · -- Verify a^2 + b^2 + c^2 + d^2 = 5
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · -- $20$ is the greatest
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, h_eq1⟩
    have h1 : (a - b)^2 + (a - c)^2 + (a - d)^2 + (b - c)^2 + (b - d)^2 + (c - d)^2 ≤ 20 := by
      nlinarith [sq_nonneg (a + b + c + d), sq_nonneg (a + b + c + d)]
    linarith