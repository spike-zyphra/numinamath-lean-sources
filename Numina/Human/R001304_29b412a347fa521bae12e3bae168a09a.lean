import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_23139 (x y z : ℝ) (hx : x = 10) (hy : y = -18) (hz : z = 35)
  (h : x^2 + y^2 + z^2 = ρ^2) (hθ : θ = arctan (y / x)) (hφ : φ = arccos (z / ρ)) :
  tan θ = -9 / 5 := by
    rw [hθ]
    rw [hx, hy]
    rw [tan_arctan]
    norm_num