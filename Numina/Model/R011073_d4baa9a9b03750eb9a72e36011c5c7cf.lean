import Mathlib

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
  use 10, 5
  constructor
  · -- Show v₀ > 0
    norm_num
  constructor
  · -- Show t > 0
    norm_num
  constructor
  · -- Show v₀ ≥ t 
    norm_num
  constructor
  · -- Show t > 1
    norm_num
  constructor
  · -- Show (v₀ * t - t * (t - 1) / 2) = 40 
    norm_num
  · -- Show t = 5
    rfl