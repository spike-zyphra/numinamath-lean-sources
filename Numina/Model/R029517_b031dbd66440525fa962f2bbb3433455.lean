import Mathlib

theorem algebra_313934 (a : ℝ) (ha : a ≠ 0) (h : (a * Real.sqrt x - 1 / Real.sqrt x)^6 = -160) :
    ∫ x in (0)..(18 / 3), (3 * x^2 - 1) = 18 := by
  have h2 : (a * Real.sqrt x - 1 / Real.sqrt x)^6 ≥ 0 := by
    positivity
  nlinarith