import Mathlib

/- Let $a_1,$ $a_2,$ $a_3$ be the first three terms of a geometric sequence.  If $a_1 = 1,$ find the smallest possible value of $4a_2 + 5a_3.$ -/
theorem algebra_13321
  (h0 : a1 = 1) :
  IsLeast {x | ∃(a2 a3 r:ℝ), a2 = a1*r ∧ a3 = a1*r^2 ∧  x = 4 *a2+ 5 * a3} (-4 / 5) := by
  -- r is common ratio, and a1=1, so a2 = r * a1, a3 = r^2 * a1
  -- 4a2 + 5a3 = 4r+5r^2 = 5 (r^2+4/5 r + 4/25) - 4/5, so minimum value is -4/5, at r=-2/5.
  rw [IsLeast, lowerBounds]; simp
  constructor
  · -- when r = -2/5, minimum value attains. so here a2 = -2/5, a3 = 4/25
    use (-2/5)
    use (4/25)
    use (-2/5)
    rw [h0]; simp; field_simp; ring_nf; simp
  · intro x a2 a3 r ha2 ha3 hx
    -- 4a2+5a3 = 4r+5r^2
    rw [hx, ha2, ha3, h0]; simp
    -- 4r+5r^2 = 5(2^2+4/5r + 4/25)-4/5 = 5(r+2/5)^2 - 4/5
    have h1: 4*r + 5*r^2 = 5*(r+(2/5))^2 - 4/5 := by ring
    have h2 := sq_nonneg (r+(2/5))
    -- therefore 5(r+2/5)^2 - 4/5 ≥ -4/5
    rw [h1]; linarith [h2]