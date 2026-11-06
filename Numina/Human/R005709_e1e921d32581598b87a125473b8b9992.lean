import Mathlib

/-
Problem: Each minute:75% chance a train arrives. If a train arrives, 75% chance she misses it. What's the probability she catches a train in 5 minutes?
-/
theorem combinatorics_609526 
    (p_train p_notice : ℝ) 
    (hp_train : p_train = 75 / 100)
    (hp_notice : p_notice = 75 / 100) :
    1 - (1 - p_train * (1 - p_notice)) ^ 5 = 1 - (13 / 16) ^ 5 := by
    
  -- Substitute probabilities
  calc
  1 - (1 - p_train * (1 - p_notice)) ^ 5 
  _= 1 - (1 - 3/4 * (1 - 3/4)) ^ 5 := by norm_num [hp_train, hp_notice]
  _ = 1 - (1 - 3/4 * 1/4) ^ 5 := by ring 
  _ = 1 - (1 - 3/16) ^ 5 := by ring
  _ = 1 - (13/16) ^ 5 := by ring 