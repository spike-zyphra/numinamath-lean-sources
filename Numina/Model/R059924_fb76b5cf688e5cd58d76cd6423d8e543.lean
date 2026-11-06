import Mathlib

theorem algebra_278164 : ⌊(10 * (2020 ^ 2021 + 2021 ^ 2022) / (2020 ^ 2020 + 2021 ^ 2021 : ℝ))⌋ = 20209 := by 
  norm_num [Int.floor_eq_iff]