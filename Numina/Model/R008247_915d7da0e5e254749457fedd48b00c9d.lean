import Mathlib
import Mathlib.Data.Real.Basic

theorem algebra_1552 (y : ℝ) :
    Real.sqrt ((-2)^2 + y^2) = Real.sqrt ((-1)^2 + (4 - y)^2) ↔ y = 13 / 8 := by
  constructor
  · -- Assume Real.sqrt ((-2)^2 + y^2) = Real.sqrt ((-1)^2 + (4 - y)^2), prove y = 13 / 8
    intro h_eq
    have h1 : (-2)^2 + y^2 = (-1)^2 + (4 - y)^2 := by
      rw [Real.sqrt_inj (by positivity) (by positivity) ] at h_eq
      nlinarith 
    nlinarith 
  · -- Assume y = 13 / 8, prove Real.sqrt ((-2)^2 + y^2) = Real.sqrt ((-1)^2 + (4 - y)^2)
    intro h_eq
    rw [h_eq]
    have h2 : Real.sqrt ((-2 : ℝ)^2 + (13 / 8)^2) = Real.sqrt ((-1 : ℝ)^2 + (4 - (13 / 8))^2) := by
      norm_num 
    exact h2