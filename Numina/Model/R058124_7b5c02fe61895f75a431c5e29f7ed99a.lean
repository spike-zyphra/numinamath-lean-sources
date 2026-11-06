import Mathlib

open Real Set
open scoped Real

theorem algebra_164225 :
  arctan (1/3) + arctan (1/5) + arctan (1/7) + arctan (1/8) = π/4 := by
  have h1 : arctan (1/3) + arctan (1/5) = arctan (4/7) := by
    rw [arctan_add]
    norm_num
    all_goals norm_num

  have h2 : arctan (4/7) + arctan (1/7) = arctan (7/9) := by
    rw [arctan_add]
    norm_num
    all_goals norm_num
  
  have h3 : arctan (7/9) + arctan (1/8) = π / 4 := by
    have h4 : arctan (7/9) + arctan (1/8) = arctan (1 : ℝ) := by 
      rw [arctan_add]
      norm_num
      all_goals norm_num
    rw [h4]
    have h5 : arctan (1 : ℝ) = π / 4 := Real.arctan_one
    rw [h5]

  have h4 : arctan (1/3) + arctan (1/5) + arctan (1/7) = arctan (7/9) := by
    linarith [h1, h2]

  linarith [h4, h3]