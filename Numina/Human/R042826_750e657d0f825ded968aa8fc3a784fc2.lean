import Mathlib

open Real Set

/- For real numbers $x,$ $y,$ and $z,$ find the minimum value of
\[2x^2 + 5y^2 + 2z^2 + 4xy - 4yz - 2z - 2x.\] -/
theorem algebra_20700 :
    IsLeast {t : ℝ | ∃ x y z, t = 2*x^2 + 5*y^2 + 2*z^2 + 4*x*y - 4*y*z - 2*z - 2*x} (-1) := by
  constructor
  -- $-1$ is a possible value
  use 1 / 2
  use 0
  use 1 / 2
  norm_num
  -- $-1$ is the least such value
  intro t tin
  rcases tin with ⟨x, y, z, teq⟩
  have teq2 : t = (x + 2 * y - z) ^ 2 + (x + z - 1) ^ 2 + y ^ 2 - 1 := by
    rw [teq]
    ring
  rw [teq2]
  nlinarith