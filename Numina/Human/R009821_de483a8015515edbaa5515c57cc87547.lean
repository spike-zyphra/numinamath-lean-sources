import Mathlib

/- The solution set of the inequality $2(x^{2}-x) < 4$ is. -/
theorem algebra_9195 (x : ℝ) : 2 * (x ^ 2 - x) < 4 ↔ -1 < x ∧ x < 2 := by
  -- notice that x^2-x = (x-1/2)^2-1/4
  have h1: 2 * (x ^ 2 - x) < 4 ↔ (x-1/2)^2 < (3/2)^2 := by
    have: (x^2-x) = (x-1/2)^2 - 1/4 := by ring
    rw [this]
    constructor
    intro h; linarith
    intro h; linarith
  rw [h1]
  have: |(3/2:ℝ)| = 3/2 := by norm_num
  constructor
  intro h
  rw [sq_lt_sq, this, abs_lt] at h
  -- |x - 1 / 2| < 3 / 2, we can decide upperbounds and lowerbounds of x
  have hl: -1 < x := by linarith [h.left]
  have hr: x < 2 := by linarith [h.right]
  exact ⟨hl,hr⟩
  -- the other direction, we argue in the same way.
  intro h
  rw [sq_lt_sq, this, abs_lt]
  have hl: -(3 / 2) < x - 1 / 2 := by linarith [h.left]
  have hr: x - 1 / 2 < 3 / 2 := by linarith [h.right]
  exact ⟨hl,hr⟩