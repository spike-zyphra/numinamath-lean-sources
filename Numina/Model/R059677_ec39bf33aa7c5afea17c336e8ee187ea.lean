import Mathlib

open Real

theorem inequalities_603290 (M : ℝ) :
    (∀ x y z : ℝ, x^4 + y^4 + z^4 + x * y * z * (x + y + z) ≥ M * (x * y + y * z + z * x)^2) ↔
    M ≤ 2 / 3 := by
  constructor
  · -- Assume inequality holds for all x, y, z, prove M ≤ 2/3.
    intro h
    have h1 := h 1 1 1
    norm_num at h1
    nlinarith
  · -- Assume M ≤ 2/3, prove the inequality holds for all x, y, z.
    intro h x y z
    have h1 : (x^4 + y^4 + z^4 + x * y * z * (x + y + z)) - (2 / 3) * (x * y + y * z + z * x)^2 ≥ 0 := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z), sq_nonneg (x * y + y * z + z * x),
        sq_nonneg (x * (y - z) + y * (z - x) + z * (x - y)),
        sq_nonneg (x^2 + y^2 + z^2 - (x * y + y * z + z * x))]
    nlinarith [sq_nonneg (x^4 + y^4 + z^4 + x * y * z * (x + y + z) - (2 / 3) * (x * y + y * z + z * x)^2), h]