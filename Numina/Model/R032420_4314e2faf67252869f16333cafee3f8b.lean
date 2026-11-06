import Mathlib

theorem inequalities_603513 (x y z : ℝ) (hx : x ∈ Set.Iic 0) (hy : y ∈ Set.Iic 0) (hz : z ∈ Set.Iic 0)
    (hsum : x + y + z = 1) :
    x * y / Real.sqrt (x * y + y * z) + y * z / Real.sqrt (y * z + z * x) +
    z * x / Real.sqrt (z * x + x * y) ≤ Real.sqrt 2 / 2 := by 
  have h1 : x ≤ 0 := by 
    simpa using hx
  have h2 : y ≤ 0 := by 
    simpa using hy
  have h3 : z ≤ 0 := by 
    simpa using hz
  have h4 : x + y + z ≤ 0 := by 
    linarith
  linarith