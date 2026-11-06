import Mathlib

open Real Set
open scoped BigOperators

/- Let $A, B$ be two distinct points on the parabola ${{y}^{2}}=2px(p>0)$, then the minimum value of ${{\left| \overrightarrow{OA}+\overrightarrow{OB} \right|}^{2}}-{{\left| \overrightarrow{AB} \right|}^{2}}$ is ___          ___. -/
theorem algebra_11782 {p : ℝ} (hp : p > 0) :
  IsLeast {x | ∃ A B : ℝ × ℝ, A ≠ B ∧ A.2^2 = 2 * p * A.1 ∧ B.2^2 = 2 * p * B.1 ∧
    x = (A.1 + B.1)^2 + (A.2 + B.2)^2 - (A.1 - B.1)^2 - (A.2 - B.2)^2} (-4 * p^2) := by
  constructor
  · -- Show that -4p² is achieved with specific points.
    use (p / 2, p), (2 * p, -2 * p)
    constructor
    · -- Verify they are distinct.
      by_contra h
      have h1 : p / 2 = 2 * p := by
        exact congrArg Prod.fst h
      have hp1 : p = 0 := by linarith
      linarith
    constructor
    · -- Verify A is on the parabola.
      ring_nf
    constructor
    · -- Verify B is on the parabola.
      ring_nf
    · -- Verify the expression evaluates to -4p².
      ring_nf
  · -- Show that -4p² is a lower bound.
    intro x hx
    rcases hx with ⟨A, B, hneq, ha, hb, hx⟩
    have h1 : (A.1 + B.1) ^ 2 + (A.2 + B.2) ^ 2 - (A.1 - B.1) ^ 2 - (A.2 - B.2) ^ 2 = 4 * (A.1 * B.1 + A.2 * B.2) := by
      ring
    rw [h1] at hx
    have h2 : A.1 * B.1 + A.2 * B.2 ≥ -p^2 := by
      nlinarith [sq_nonneg (A.2 * B.2 + 2 * p^2), sq_nonneg (A.2 * p - B.2 * p), sq_nonneg (A.2 + B.2), sq_nonneg (A.2 - B.2), sq_nonneg (A.1 - B.1), sq_nonneg (A.2 - B.2), mul_pos hp hp]
    nlinarith [h2]