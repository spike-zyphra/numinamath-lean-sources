import Mathlib

theorem algebra_262167 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y + z - x * y * z < 0 ∧ x * y + y * z + z * x - 3 < 0) ↔ False := by
  constructor
  · -- Assume both expressions are negative, derive False
    intro h
    rcases h with ⟨h1, h2⟩
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  · -- Assume False, derive anything (trivial)
    intro h
    cases h