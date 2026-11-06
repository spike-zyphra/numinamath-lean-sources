import Mathlib

open Real

theorem inequalities_39741 : IsGreatest {M : ℝ | ∀ x y z : ℝ, x^4 + y^4 + z^4 + x * y * z * (x + y + z) ≥ M * (x * y + y * z + z * x)^2} (2 / 3) := by 
  constructor
  · -- Show 2/3 is in the set 
    intro x y z
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              sq_nonneg (x + y + z), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
              sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y))
            ]
  · -- Show 2/3 is greatest in the set
    intro M h
    have h1 := h 1 1 1
    nlinarith