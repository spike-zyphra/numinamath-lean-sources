import Mathlib

theorem algebra_122063 {x : ℝ} (hx : x > 0) (h : x - √(2022 / x) = 2023) :
    x - √(2022 * x) + 2023 = 2024 := by

  have h1 : x - √(2022 / x) = 2023 := h
  have h2 : √(2022 / x) = x - 2023 := by linarith [h1]

  have h3 : √(2022 / x) ≥ 0 := by positivity
  have h4 : x - 2023 ≥ 0 := by linarith [h2, h3]
  have h5 : (√(2022 / x)) ^ 2 = 2022 / x := by
    rw [Real.sq_sqrt]
    have : (2022 / x) ≥ 0 := by
      apply div_nonneg
      norm_num
      linarith [show 0 < x by linarith]
    linarith

  have h6 : (x - 2023) ^ 2 = 2022 / x := by
    calc
      (x - 2023) ^ 2 = (√(2022 / x)) ^ 2 := by
        rw [h2]
      _ = 2022 / x := h5

  have h7 : (x - 2023) ^ 2 * x = 2022 := by
    have h8 : (x - 2023) ^ 2 = 2022 / x := h6
    have : (x - 2023) ^ 2 * x = 2022 := by
      calc
        (x - 2023) ^ 2 * x = (2022 / x) * x := by
          rw [h8]
        _ = 2022 := by
          field_simp [show x ≠ 0 by linarith]
          <;> nlinarith
    linarith

  have h8 : x - √(2022 * x) + 2023 = 2024 := by
    have h9 : √(2022 * x) ≥ 0 := by positivity
    have h10 : (√(2022 * x)) ^ 2 = 2022 * x := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [Real.sqrt_nonneg (2022 * x), Real.sqrt_nonneg (2022 / x), h6, h7, mul_nonneg (Real.sqrt_nonneg (2022 * x)) (Real.sqrt_nonneg (2022 / x)), Real.sq_sqrt (show (2022 * x : ℝ) ≥ 0 by nlinarith), Real.sq_sqrt (show (2022 / x : ℝ) ≥ 0 by positivity) ]

  linarith [h8]