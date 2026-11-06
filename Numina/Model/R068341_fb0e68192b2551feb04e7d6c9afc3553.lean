import Mathlib

open Real Set

theorem calculus_73193 : arctan (1 / 2) + arctan (1 / 3) = π / 4 := by 
  have h1 : arctan (1 / 2) + arctan (1 / 3) = arctan (1 : ℝ) := by 
    rw [arctan_add]
    all_goals norm_num
  rw [h1]
  exact arctan_one