import Mathlib

theorem algebra_325787 : Real.sqrt (2018 * 2021 * 2022 * 2023 + 2024^2) - 2024^2 = -12138 := by
  have h1 : Real.sqrt (2018 * 2021 * 2022 * 2023 + 2024^2) = (2021^2 - 3 : ℝ) := by
    have h2 : (2018 * 2021 * 2022 * 2023 + 2024^2 : ℝ) = (2021^2 - 3) ^ 2 := by
      norm_num
    rw [h2]
    rw [Real.sqrt_sq (by norm_num)]
  rw [h1]
  norm_num