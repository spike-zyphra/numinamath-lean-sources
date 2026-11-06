import Mathlib

theorem algebra_170506 (x y z : ℤ) :
    IsSquare (9 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 - 8 * (x + y + z) * (x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z)) := by
  have h1 : 9 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 - 8 * (x + y + z) * (x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z) = (x ^ 2 + y ^ 2 + z ^ 2 - 4 * (x * y + x * z + y * z)) ^ 2 := by
    ring_nf
  rw [h1]
  exact ⟨x ^ 2 + y ^ 2 + z ^ 2 - 4 * (x * y + x * z + y * z), by ring⟩