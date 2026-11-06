import Mathlib
/- Find the maximum value of $x+y$, given that $x^{2}+y^{2}-3 y-1=0$. -/
theorem algebra_608565 : IsGreatest {a : ℝ | ∃ x y : ℝ, a = x + y ∧ x ^ 2 + y ^ 2 - 3 * y - 1 = 0} ((√26 + 3) / 2):= by
  constructor
  -- First part: Prove that this point exists (membership)
  .
    simp
    -- Use x = √26/4 and y = √26/4 + 3/2 as the solution
    use (√26 / 4)
    use (√26 / 4 + 3 / 2)
    constructor
    -- Prove the sum equals (√26 + 3)/2
    .
      linarith
    -- Prove these values satisfy the original equation
    .
      ring_nf
      field_simp
      linarith
  -- Second part: Prove this is the maximum value
  .
    simp [upperBounds]
    intro a x y ha h
    subst a
    -- Rewrite equation to complete square form for y
    replace h : x ^ 2 + (y - 3 / 2) ^ 2 = 13 / 4:= by linarith
    -- Use the fact that (y - 3/2 - x)^2 ≥ 0 to establish inequality
    replace h : (x + y - 3 / 2) ^ 2 ≤ 26 / 4:= by
      have g1 : (y - 3 / 2 - x) ^ 2 ≥ 0:= by positivity
      linarith
    -- Simplify using square root of 26
    rw [show (26 : ℝ) / 4 = (√26 / 2) ^ 2 by ring_nf ; field_simp ; linarith] at h
    -- Convert to absolute value inequality
    replace h : |x + y - 3 / 2| ≤ |√26 / 2|:= by exact sq_le_sq.mp h
    -- Simplify absolute value since √26/2 is positive
    rw [show |√26 / 2| = √26 / 2 by exact abs_of_nonneg (by positivity)] at h
    -- Use property of absolute value: |a| ≥ a
    have h1 : |x + y - 3 / 2| ≥ x + y - 3 / 2:= by exact le_abs_self (x + y - 3 / 2)
    linarith
