import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_599509 :
  IsLeast {t : ℝ | ∃ x y z, t = x^2 - 2 * x + 2 * y^2 + 3 * z^2 ∧ x + y + z = 2} (-5 / 11) := by
  constructor
  · -- First part: show that $-5/11$ is achievable
    use 17 / 11
    use 3 / 11
    use 2 / 11
    constructor
    -- Compute $T$ at $(17/11, 3/11, 2/11)$
    -- $x^2 - 2 x + 2 y^2 + 3 z^2$
    -- $(17/11)^2 -2*(17/11) + 2*(3/11)^2 + 3*(2/11)^2$
    -- $(289/121) - (34/11) + (2*(9/121)) + (3*(4/121))$
    -- numerator sum equals $289-34*11+ 288+8 = -55$
    norm_num
    -- Show $x + y + z = 2$
    norm_num
  · -- Show that $-5/11$ is indeed the minimum
    intro t ht
    rcases ht with ⟨x, y, z, hht1, hht2⟩
    -- We need to prove that $T(x,y,z) \geq -5/11$
    -- Given $x+y+z=2$, show $t = x^2 -2x + 2y^2 + 3z^2 \geq -5/11$
    have h1 : x + y + z = 2 := hht2
    -- Use Lagrange multipliers to derive the minimum point
    -- Now, with all the relations between $x$, $y$, and $z$
    -- The solution to these Lagrange conditions will give the minimum
    nlinarith [sq_nonneg (x - 17 / 11),
      sq_nonneg (y - 3 / 11),
      sq_nonneg (z - 2 / 11),
      sq_nonneg ((x -17/11) *1 + (y -3/11) *1 + (z -2/11)*1),
      sq_nonneg ((x -17/11) - 2 * (y -3/11)),
      sq_nonneg ((x -17/11) - 3 * (z -2/11)),
      sq_nonneg ((y -3/11) - (2/3) * (z -2/11)),
      sq_nonneg (2 * (x -17/11) - 4 * (y -3/11) + 6 * (z -2/11))
      ]