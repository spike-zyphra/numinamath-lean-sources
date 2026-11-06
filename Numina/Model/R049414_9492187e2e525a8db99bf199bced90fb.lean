import Mathlib

theorem algebra_254973 {a d : ℤ} (hd : d ≠ 0) :
    ∃ n, a * (a + d) * (a + 2 * d) * (a + 3 * d) + d ^ 4 = n ^ 2 := by
  use a^2 + 3 * a * d + d^2
  ring_nf