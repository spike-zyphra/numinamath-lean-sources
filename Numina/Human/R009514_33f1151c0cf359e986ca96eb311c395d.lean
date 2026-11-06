import Mathlib

/- If $z=3+4i$, find $z^2$. (Note that $i^2 = -1.$) -/
theorem algebra_11567 {z : ℂ} (hz : z = 3 + 4 * .I) : z ^ 2 = -7 + 24 * .I := by
  rw [hz]
  ring
  simp [sq]
  ring