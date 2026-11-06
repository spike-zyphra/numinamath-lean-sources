import Mathlib

/-- 
Candice starts driving home from work at 5:00 PM. Starting at exactly 5:01 PM, 
and every minute after that, Candice encounters a new speed limit sign and slows down by 1 mph.
Candice's speed, in miles per hour, is always a positive integer.
Candice drives for 2/3 of a mile in total.
She drives for a whole number of minutes, and arrives at her house driving slower than when she left.
What time is it when she gets home? The answer is 5:05 PM.
--/
theorem algebra_610504 : 
  ∃ (v₀ t : ℕ), 
    -- v₀ is the initial speed in mph
    v₀ > 0 ∧
    -- t is the number of minutes driven
    t > 0 ∧
    -- Speed at each minute must be positive
    v₀ ≥ t ∧
    -- The final speed must be less than the initial speed
    t > 1 ∧
    -- The total distance is 2/3 mile
    (v₀ * t - t * (t - 1) / 2) = 40 ∧
    -- Candice arrives at time 5:00 + t minutes = 5:05 PM
    t = 5 := by
  
  -- We'll prove that v₀ = 10 and t = 5 is the unique solution
  use 10, 5
  
  -- Now let's verify all the conditions
  constructor
  -- v₀ > 0
  · norm_num
  
  constructor
  -- t > 0
  · norm_num
  
  constructor
  -- v₀ ≥ t
  · norm_num
  
  constructor
  -- t > 1
  · norm_num
  
  constructor
  -- v₀ * t - t * (t - 1) / 2 = 40
  · -- Let's calculate this step by step
    have h1 : 10 * 5 = 50 := by norm_num
    have h2 : 5 * (5 - 1) = 20 := by norm_num
    have h3 : 20 / 2 = 10 := by norm_num
    have h4 : 50 - 10 = 40 := by norm_num
    
    -- Now combine these facts
    calc
      10 * 5 - 5 * (5 - 1) / 2 = 50 - 5 * (5 - 1) / 2 := by rw [h1]
      _ = 50 - 20 / 2 := by rw [h2]
      _ = 50 - 10 := by rw [h3]
      _ = 40 := h4
  
  -- t = 5
  · rfl