import Mathlib

theorem algebra_231163 (x y z : ℤ) (h : x + y + z = 0) :
    IsSquare (2 * (x ^ 4 + y ^ 4 + z ^ 4)) := by
  have hz : z = -x - y := by linarith
  rw [hz]
  have h1 : 2 * (x ^ 4 + y ^ 4 + (-x - y) ^ 4) =
      (2 * (x ^ 2 + x * y + y ^ 2)) ^ 2 := by
    ring_nf
  rw [h1]
  exact ⟨2 * (x ^ 2 + x * y + y ^ 2), by ring⟩