import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_154861 {x : ℝ} (hx : x - 2 > 0) : x ∈ Ioi 2 := by 
  exact mem_Ioi.mpr (show x > 2 by linarith)