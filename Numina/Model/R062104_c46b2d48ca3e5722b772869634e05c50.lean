import Mathlib

open Real Set

theorem calculus_15040 (x : ℝ) (hx : x = sqrt 3 / 2) :
    arccos x = π / 6 := by 
  rw [hx]
  have h1 : cos (π / 6) = sqrt 3 / 2 := by 
    exact Real.cos_pi_div_six
  have h2 : arccos (sqrt 3 / 2) = π / 6 := by
    rw [← h1]
    apply arccos_cos
    all_goals linarith [Real.pi_pos]
  exact h2