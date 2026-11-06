import Mathlib

/-There are eight furlongs in a mile. There are two weeks in a fortnight. The British cavalry traveled 2800 furlongs in a fortnight. How many miles per day did the cavalry average?-/
theorem algebra_20099 (furlongs_per_mile : ℝ) (h : furlongs_per_mile = 8) (days_in_fortnight : ℝ)
    (h' : days_in_fortnight = 14) (furlongs_traveled : ℝ) (h'' : furlongs_traveled = 2800) :
    (furlongs_traveled / (days_in_fortnight * furlongs_per_mile)) = 25 := by norm_num [h, h', h'']