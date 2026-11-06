import Mathlib

theorem algebra_163855 (dining_hall_grill : ℕ) (h : dining_hall_grill = 135) :
    dining_hall_grill + (dining_hall_grill / 3) + (2 * (dining_hall_grill / 3)) = 270 := by 
  subst h
  all_goals norm_num