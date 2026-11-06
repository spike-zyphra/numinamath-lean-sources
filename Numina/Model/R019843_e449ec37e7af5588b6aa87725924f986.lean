import Mathlib

theorem algebra_103591 {x y z A : ℤ} (hA : A = x * y + y * z + z * x)
    (h : A = (x + 1) * (y - 2) + (y - 2) * (z - 2) + (z - 2) * (x + 1)) :
    ∃ n, (-1) * A = n ^ 2 := by
  have h1 : z = -4 * x - y := by
    nlinarith [hA, h]
  have h2 : A = - (2 * x + y) ^ 2 := by
    rw [hA]
    rw [show z = -4 * x - y by linarith [h1]]
    nlinarith
  use 2 * x + y
  rw [h2]
  all_goals
    ring