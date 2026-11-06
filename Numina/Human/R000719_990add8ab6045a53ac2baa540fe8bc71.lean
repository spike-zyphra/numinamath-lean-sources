import Mathlib

/- The workers in a factory produce widgets and whoosits. For each product, production time is constant and identical for all workers, but not necessarily equal for the two products. In one hour, 100 workers can produce 300 widgets and 200 whoosits. In two hours, 60 workers can produce 240 widgets and 300 whoosits. In three hours, 50 workers can produce 150 widgets and $m$ whoosits. Find $m$.

The final answer is $ \boxed{450} $-/
theorem algebra_14264 {widget whoosit : ℝ} (ha : 0 < widget) (hb : 0 < whoosit)
  (h1 : 100  = 300 * widget + 200 * whoosit) (h2 : 60 * 2 = 240 * widget + 300 * whoosit)
  (h3 : 50 * 3 = 150 * widget + m * whoosit) : m = 450 := by
    -- Let `widget` be the time required for a worker to produce a widget, and let
    -- `whoosit` be the time required for a worker to produce a whoosit, so we have above three equations.
    -- solving them we get m = 450.
    nlinarith
