import Mathlib

/- The workers in a factory produce widgets and whoosits. For each product, production time
is constant and identical for all workers, but not necessarily equal for the two products.
In one hour, 100 workers can produce 300 widgets and 200 whoosits. In two hours,60 workers
can produce 240 widgets and 300 whoosits. In three hours, 50 workers can produce 150 widgets
and m whoosits. Find m. -/
theorem algebra_93618 (x y:ℝ) (hxy_pos: 0 < x ∧ 0 < y)
(h1: 100 = 300 * x + 200 * y)
(h2: 2*60 = 240 * x + 300 * y)
(h3: 3*50 = 150 * x + m * y) :
m = 450 := by
  -- solve first two equations for x and y
  have hx1: x = (100-200*y)/300 := by linarith
  rw [hx1] at h2 h3
  ring_nf at h2 h3
  have hy: y = (120-80)/140 := by linarith
  rw [hy] at h3
  -- linarith can go from h3 to ⊢
  linarith