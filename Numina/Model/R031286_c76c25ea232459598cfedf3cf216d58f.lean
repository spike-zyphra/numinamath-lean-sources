import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_2330 {z : ℂ} (hz : abs (z - I * z) ^ 2 = 50) (hz' : abs (z - I * z) ^ 2 = 93) :
    abs (z - I * (z.1 - I * z.2)) ^ 2 = 136 := by 
  have h1 : abs (z - I * z) ^ 2 = 50 := hz
  have h2 : abs (z - I * z) ^ 2 = 93 := hz'
  have h3 : (50 : ℝ) = (93 : ℝ) := by 
    linarith [h1, h2]
  linarith