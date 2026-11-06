import Mathlib

theorem algebra_104436 {x : ℝ} (h : (2019-2020*x)*(2021-2020*x)=2022) :
    (2019-2020*x)^2+(2021-2020*x)^2=4048 := by
  have eq1 : (2021 - 2020 * x) = (2019 - 2020 * x) + 2 := by
    ring
  rw [eq1] at h ⊢
  nlinarith [sq_nonneg ((2019 - 2020 * x) + 1)]