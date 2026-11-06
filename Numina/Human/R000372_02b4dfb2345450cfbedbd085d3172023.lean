import Mathlib

/- The solution set of the inequality $|x-2|+|x+3| \geq 7$ is-/
theorem algebra_9260 (x : ℝ) :
    abs (x - 2) + abs (x + 3) ≥ 7 ↔ x ≤ -4 ∨ x ≥ 3 := by
  -- We split into if and only if parts.
  constructor
  . intro hx
    contrapose! hx
    by_cases hx1 : 2 < x
    -- If $x>2$, then the expression inside abs are positive.
    . rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    -- If $x<-3$, then the expression inside abs are negtive.
    by_cases hx2 : x < -3
    . rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      linarith
    -- If $-3 \leq x \leq 2$, then $|x-2|=2-x$ and $|x+3|=x+3$.
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
  rintro (hx | hx)
  -- If $x\leq -4$, it's clear that $|x-2|+|x+3|\geq 7$.
  . rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith
  -- If $x\geq 3$, it's clear that $|x-2|+|x+3|\geq 7$.
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
  linarith
