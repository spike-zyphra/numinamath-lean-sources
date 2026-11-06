import Mathlib

/- Given real numbers $a$, $b$, $c$ satisfying $a^{2}+b^{2}+c^{2}=3$, the maximum value of $2ab+3c$ is ______. -/
theorem algebra_9290 : IsGreatest {x : ℝ | ∃ a b c : ℝ, a^2 + b^2 + c^2 = 3 ∧ 2 * a * b + 3 * c = x} (21 / 4) := by
  -- Split the problem into two parts
  -- 1. Prove that 21/4 can be achieved
  -- 2. Prove that 21/4 is the maximum value
  constructor <;> simp [upperBounds]
  . -- Set a = b = √(3/8), c = 3/2
    use √(3/8), √(3/8), 3/2
    constructor
    . rw [Real.sq_sqrt] <;> norm_num
    . rw [mul_assoc, ← sq, Real.sq_sqrt] <;> norm_num
  . intro x a b c h hx
    subst hx
    -- (a - b)^2 ≥ 0 and (c - 3/2)^2 ≥ 0 are enough to prove the inequality linearly
    have h1 : 0 ≤ (a - b)^2 := sq_nonneg _
    have h2 : 0 ≤ (c - 3/2)^2 := sq_nonneg _
    linarith
