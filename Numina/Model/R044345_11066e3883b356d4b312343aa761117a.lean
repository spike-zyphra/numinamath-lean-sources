import Mathlib

open Real Set
open scoped Real

theorem algebra_12974 {x : ℝ} (hx : x = arctan (1/2) + arctan (1/3)) (hx1 : 0 < x) (hx2 : x < π) :
    x = π/4 := by
  have h1 : x = arctan (1 / 2) + arctan (1 / 3) := by
    rw [hx]
  have h2 : arctan (1 / 2) + arctan (1 / 3) = Real.arctan (1) := by 
    rw [arctan_add]
    all_goals norm_num
  have h3 : x = Real.arctan (1) := by 
    linarith [h1, h2]
  have h4 : Real.arctan (1) = Real.pi / 4 := Real.arctan_one
  rw [h3]
  rw [h4]
  all_goals linarith