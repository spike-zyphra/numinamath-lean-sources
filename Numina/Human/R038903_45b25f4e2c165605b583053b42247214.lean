import Mathlib
/- Find the largest real number $\lambda$ such that $a^{2}+b^{2}+c^{2}+d^{2} \geq a b+\lambda b c+c d$ for all real numbers $a, b, c, d$. -/
theorem algebra_609153 : IsGreatest {t : ℝ | ∀ a b c d : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ a * b + t * b * c + c * d} (3 / 2):= by
  constructor
  -- First part: prove that 3/2 satisfies the inequality
  .
    simp
    intro a b c d
    -- Use three non-negative square terms to prove the inequality
    -- (a - b/2)² ≥ 0
    have g1 : (a - b / 2) ^ 2 ≥ 0:= by positivity
    -- (d - c/2)² ≥ 0
    have g2 : (d - c / 2) ^ 2 ≥ 0:= by positivity
    -- (b - c)² ≥ 0
    have g3 : (b - c) ^ 2 ≥ 0:= by positivity
    linarith
  -- Second part: prove that no larger value can satisfy the inequality
  .
    simp [upperBounds]
    intro x h
    -- Use a counterexample with specific values: a=1, b=2, c=2, d=1
    specialize h 1 2 2 1
    linarith
