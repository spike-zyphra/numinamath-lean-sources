import Mathlib

theorem other_192900 (capacity : ℝ) (distance : ℝ) (consumption_rate : ℝ) (min_fuel : ℝ)
    (h₀ : capacity = 50) (h₁ : distance = 2560) (h₂ : consumption_rate = 8 / 100) (h₃ : min_fuel = 6) :
    ⌈(distance / (capacity - min_fuel)) * consumption_rate⌉ - 1 = 4 := by
  rw [h₀, h₁, h₂, h₃]
  norm_num [Int.ceil_eq_iff]