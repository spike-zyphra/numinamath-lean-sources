import Mathlib

open Real Set
open scoped BigOperators

/- If real numbers $a$, $b$ satisfy the conditions $\begin{cases}a+b-2\geqslant 0 \\ b-a-1\leqslant 0 \\ a\leqslant 1 \end{cases}$, then the maximum value of $\frac{a+2b}{2a+b}$ is ___        ___. -/
theorem inequalities_11403 :
  IsGreatest {x | ∃ a b : ℝ, x = (a + 2 * b) / (2 * a + b) ∧
    a + b - 2 ≥ 0 ∧ b - a - 1 ≤ 0 ∧ a ≤ 1} (7 / 5) := by
  constructor 
  · use (1 / 2 : ℝ)
    use (3 / 2 : ℝ)
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · intro x hx
    rcases hx with ⟨a, b, heq, h1, h2, h3⟩
    have h4 : 2 * a + b > 0 := by
      linarith
    have h5 : (a + 2 * b) / (2 * a + b) ≤ 7 / 5 := by
      apply (div_le_iff' (by linarith)).mpr
      linarith
    linarith [heq, h5]