import Mathlib

theorem algebra_207698 (inflation_rate : ℝ) (h : inflation_rate > 0) (real_value : ℝ)
    (h' : real_value > 0) (h'' : (1 + inflation_rate / 100) * real_value = (1 - 20 / 100) * (1 + 16 / 100) * real_value) :
    (1 - 20 / 100) * (1 + 16 / 100) * real_value = (1 - 31 / 100) * real_value := by
  nlinarith