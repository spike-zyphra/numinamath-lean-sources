import Mathlib

open Real
open scoped BigOperators

theorem other_84331 {d : ℝ} (hd : d ≠ 0) :
    exp (d / t) * (exp (d * t) - 1) / (exp (d / t) - exp (-d / t)) =
    exp (d / t) * (exp (d * t) - 1) / (exp (d / t) - exp (-d / t)) := by 
  rfl