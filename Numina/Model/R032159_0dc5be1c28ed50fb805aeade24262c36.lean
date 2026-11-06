import Mathlib

open Real

theorem algebra_288387 :
    π * logb 2018 (sqrt 2) + sqrt 2 * logb 2018 π +
    π * logb 2018 (1 / sqrt 2) + sqrt 2 * logb 2018 (1 / π) = 0 := by
  have h1 : logb 2018 (1 / sqrt 2) = - logb 2018 (sqrt 2) := by 
    simp [logb_div, logb_one]
  have h2 : logb 2018 (1 / π) = - logb 2018 π := by 
    simp [logb_div, logb_one]
  rw [h1, h2]
  ring