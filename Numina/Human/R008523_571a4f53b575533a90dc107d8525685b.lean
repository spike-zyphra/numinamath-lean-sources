import Mathlib

/-Let $r$ be a root of $x^2 + 5x + 7 = 0.$  Compute
\[(r - 1)(r + 2)(r + 6)(r + 3).\]-/
theorem algebra_21648 {r : ℝ} (hr : r ^ 2 + 5 * r + 7 = 0) :
    (r - 1) * (r + 2) * (r + 6) * (r + 3) = 13 := by
  -- simply calculation
  calc
    (r - 1) * (r + 2) * (r + 6) * (r + 3) = (r - 1) * (r + 6) * (r + 3) * (r + 2) := by ring_nf
    _ = (r ^ 2 + 5 * r - 6) * (r ^ 2 + 5 * r + 6) := by ring_nf
    _ = ((r ^ 2 + 5 * r + 7) - 13) * ((r ^ 2 + 5 * r + 7) - 1) := by ring_nf
    _ = 13 := by rw [hr]; norm_num