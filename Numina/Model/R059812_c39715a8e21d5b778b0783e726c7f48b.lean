import Mathlib

open Real Set

theorem algebra_252703 (x y : ℝ) :
    cos (x^2) + cos (y^2) - cos (x * y) ∈ Icc (-3) 3 := by
  constructor
  · -- Show that cos(x^2) + cos(y^2) - cos(x * y) ≥ -3
    have h1 : -1 ≤ cos (x^2) := Real.neg_one_le_cos (x^2)
    have h2 : -1 ≤ cos (y^2) := Real.neg_one_le_cos (y^2)
    have h3 : -1 ≤ cos (x * y) := Real.neg_one_le_cos (x * y)
  --   need to prove that cos(x^2) + cos(y^2) - cos(x * y) ≥ -3
  --   cos(x^2) ≥ -1
  --   cos(y^2) ≥ -1
  --   -cos(x * y) ≤ -1
    linarith [h1, h2, Real.cos_le_one (x * y)]
  · -- Show that cos(x^2) + cos(y^2) - cos(x * y) ≤ 3
    have h4 : cos (x^2) ≤ 1 := Real.cos_le_one (x^2)
    have h5 : cos (y^2) ≤ 1 := Real.cos_le_one (y^2)
    have h6 : cos (x * y) ≥ -1 := Real.neg_one_le_cos (x * y)
  --   need to prove that cos(x^2) + cos(y^2) - cos(x * y) ≤ 3
  --   cos(x^2) ≤ 1
  --   cos(y^2) ≤ 1
  --   -cos(x * y) ≤ 1
    linarith [h4, h5, h6]