import Mathlib
open Mathlib
theorem algebra_95437 (x y k : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x > y) (hk : 0 < k) :
(x + k) - (y - k) > x - y := by
  have h1 : (x + k) - (y - k) = x - y + 2 * k := by
    ring
  rw [h1]
  linarith