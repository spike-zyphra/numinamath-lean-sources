import Mathlib

/- The solution set of the inequality $(x-2)(3-x) > 0$ is $\boxed{\text{answer}}$.-/
theorem algebra_9417 (x : ℝ) : 0 < (x - 2) * (3 - x) ↔ 2 < x ∧ x < 3 := by
  -- It's obvious that $ab > 0$ if and only if $a>0,b>0$ or $a<0,b<0$.
  rw [mul_pos_iff]
  -- We split into two parts.
  constructor
  -- The if part, we deduce $2 < x < 3$ from $(x-2)(3-x) > 0$.
  . rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    all_goals constructor <;> linarith
  -- The only if part, we deduce $(x-2)(x-3) > 0$ from $2 < x < 3$.
  . rintro ⟨h1, h2⟩
    left
    constructor <;> linarith
