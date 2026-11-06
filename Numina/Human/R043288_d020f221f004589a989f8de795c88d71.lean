import Mathlib.Data.Int.Defs
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

/- 416. The product of two numbers, each of which is the sum of four squares, is also equal to the sum of four square
s.

Euler's identity. -/
theorem number_theory_221928 {a b : ℤ} (ha : ∃ x y z w, a = x^2 + y^2 + z^2 + w^2)
    (hb : ∃ u v w x, b = u^2 + v^2 + w^2 + x^2) :
    ∃ y z w u, a * b = y^2 + z^2 + w^2 + u^2 := by
  -- Introduce variables
  rcases ha with ⟨p, q ,r, s, ha⟩
  rcases hb with ⟨p', q', r', s', hb⟩
  -- Use an explicit construction that will satisfy the conditions of the problem
  use p*p' + q*q' + r*r' + s*s'
  use p*q' + r*s' - q*p' - s*r'
  use p*r' + s*q' - q*s' - r*p'
  use p*s' + q*r' - s*p' - r*q'
  rw [ha, hb]
  -- Show that the construction does indeed work
  ring