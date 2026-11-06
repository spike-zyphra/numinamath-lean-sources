import Mathlib

/- Solve the equation: $x^{2}-4x-8=0$. -/
theorem algebra_8999 (x : ℝ) : x^2 - 4 * x - 8 = 0 ↔ x = 2 + 2 * Real.sqrt 3 ∨ x = 2 - 2 * Real.sqrt 3 := by
  -- Split the goal into two implications
  constructor <;> intro h
  . -- First implication
    -- We have x^2 - 4 * x - 8 = 0
    -- We can rewrite this as (x - 2)^2 = 2^2 * 3
    replace h : (x - 2) ^ 2 = (√(2^2 * 3))^2 := by linarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2^2 * 3)]
    -- So x - 2 = ± 2 * √3
    rw [sq_eq_sq_iff_eq_or_eq_neg] at h
    simp at h
    -- Trivial case analysis
    obtain h | h := h
    . left
      linarith
    . right
      linarith

  . -- Second implication
    -- We need to show x^2 - 4 * x - 8 = 0
    -- We rewrite this as (x - 2)^2 = 12
    suffices _ : (x - 2) ^ 2 = 12 by linarith
    -- Case analysis on x = 2 + 2 * √3 or x = 2 - 2 * √3
    obtain h | h := h
    all_goals
      -- Plug in the value of x and simplify
      subst x
      ring_nf
      norm_num
