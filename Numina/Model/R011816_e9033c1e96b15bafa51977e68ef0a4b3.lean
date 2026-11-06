import Mathlib

theorem algebra_153725 (a b c : ℝ) :
    ∃ x : ℝ, |x| ≤ 1 ∧ |x ^ 3 + a * x ^ 2 + b * x + c| ≥ 1 / 4 := by
  by_contra h
  push_neg at h
  have h0 : |(1:ℝ) ^ 3 + a * (1:ℝ) ^ 2 + b * (1:ℝ) + c| < 1 / 4 := by
    apply h
    norm_num
  have h1 : |(-1:ℝ) ^ 3 + a * (-1:ℝ) ^ 2 + b * (-1:ℝ) + c| < 1 / 4 := by
    apply h
    norm_num
  have h2 : |(0:ℝ) ^ 3 + a * (0:ℝ) ^ 2 + b * (0:ℝ) + c| < 1 / 4 := by
    apply h
    norm_num
  have h3 : |(1/2:ℝ) ^ 3 + a * (1/2:ℝ) ^ 2 + b * (1/2:ℝ) + c| < 1 / 4 := by
    apply h
    norm_num [abs_le]
  have h4 : |(-1/2:ℝ) ^ 3 + a * (-1/2:ℝ) ^ 2 + b * (-1/2:ℝ) + c| < 1 / 4 := by
    apply h
    norm_num [abs_le]
  cases' abs_lt.mp h0 with h01 h02
  cases' abs_lt.mp h1 with h11 h12
  cases' abs_lt.mp h2 with h21 h22
  cases' abs_lt.mp h3 with h31 h32
  cases' abs_lt.mp h4 with h41 h42
  linarith