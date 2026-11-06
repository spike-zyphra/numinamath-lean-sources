import Mathlib

theorem algebra_21330 : IsGreatest { c : ℝ | ∃x, 2 * x^2 + 5 * x + c = 0 } (25 / 8) := by
  constructor
  · -- Show that 25/8 is in the set
    use -5 / 4
    norm_num
  · -- Show that 25/8 is the greatest element in the set
    intro c hc
    rcases hc with ⟨x, hx⟩
    -- From the equation $2 * x^2 + 5 * x + c = 0$, we can deduce $c \leq 25/8$
    have h : 2 * x^2 + 5 * x + c = 0 := by linarith
    nlinarith [sq_nonneg (x + 5 / 4)]