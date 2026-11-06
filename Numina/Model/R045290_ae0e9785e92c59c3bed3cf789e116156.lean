import Mathlib

theorem algebra_253479 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz₁: 0 < x*y*z-3 + Real.logb 5 x) (hxyz₂: 0 < x*y*z-3 + Real.logb 5 y) (hxyz₃: 0 < x*y*z-3 + Real.logb 5 z)
    (h1 : Real.logb 2 (x * y * z - 3 + Real.logb 5 x) = 5) (h2 : Real.logb 3 (x * y * z - 3 + Real.logb 5 y) = 4)
    (h3 : Real.logb 4 (x * y * z - 3 + Real.logb 5 z) = 4) :
    Real.logb 5 (x * y * z) = 3 := by

  have h1' : x * y * z - 3 + Real.logb 5 x = 32 := by
    have h1_eq : Real.logb 2 (x * y * z - 3 + Real.logb 5 x) = 5 := h1
    rw [Real.logb_eq_iff_rpow_eq] at h1_eq
    · linarith
    all_goals linarith

  have h2' : x * y * z - 3 + Real.logb 5 y = 81 := by
    have h2_eq : Real.logb 3 (x * y * z - 3 + Real.logb 5 y) = 4 := h2
    rw [Real.logb_eq_iff_rpow_eq] at h2_eq
    · nlinarith
    all_goals nlinarith

  have h3' : x * y * z - 3 + Real.logb 5 z = 256 := by
    have h3_eq : Real.logb 4 (x * y * z - 3 + Real.logb 5 z) = 4 := h3
    rw [Real.logb_eq_iff_rpow_eq] at h3_eq
    · nlinarith
    all_goals nlinarith

  have h4 : Real.logb 5 x = 32 - (x * y * z - 3) := by linarith [h1']
  have h5 : Real.logb 5 y = 81 - (x * y * z - 3) := by linarith [h2']
  have h6 : Real.logb 5 z = 256 - (x * y * z - 3) := by linarith [h3']

  have h7 : Real.logb 5 x + Real.logb 5 y + Real.logb 5 z = Real.logb 5 (x * y * z) := by 
    rw [Real.logb_mul (by positivity) (by positivity)]
    rw [Real.logb_mul (by positivity) (by positivity)]

  have h8 : Real.logb 5 x + Real.logb 5 y + Real.logb 5 z = (32 + 81 + 256) - 3 * (x * y * z - 3) := by
    linarith [h4, h5, h6]

  have h9 : Real.logb 5 (x * y * z) = (32 + 81 + 256) - 3 * (x * y * z - 3) := by
    linarith [h7, h8]

  have h12 : x * y * z = 125 := by
    by_cases h13 : x * y * z < 125
    · -- Assume x * y * z < 125
      have h14 : Real.logb 5 (x * y * z) < 3 := by
        have h15 : x * y * z < (125 : ℝ) := h13
        have h17 : Real.logb 5 (x * y * z) < Real.logb 5 (125 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals nlinarith [show 0 < x * y * z by positivity, show 0 < (125 : ℝ) by norm_num]
        have h18 : Real.logb 5 (125 : ℝ) = (3 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        nlinarith [h17, h18]

      have h11 : Real.logb 5 (x * y * z) = (32 + 81 + 256) - 3 * (x * y * z - 3) := h9
      nlinarith [h14, h11]

    by_cases h14 : x * y * z > 125
    · -- Assume x * y * z > 125
      have h15 : Real.logb 5 (x * y * z) > 3 := by
        have h16 : x * y * z > (125 : ℝ) := h14
        have h18 : Real.logb 5 (x * y * z) > Real.logb 5 (125 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals nlinarith [show 0 < x * y * z by positivity, show 0 < (125 : ℝ) by norm_num]
        have h19 : Real.logb 5 (125 : ℝ) = (3 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        nlinarith [h18, h19]

      have h11 : Real.logb 5 (x * y * z) = (32 + 81 + 256) - 3 * (x * y * z - 3) := h9
      nlinarith [h15, h11]

    linarith

  have h10 : Real.logb 5 (x * y * z) = 3 := by
    have h11 : Real.logb 5 (x * y * z) = (32 + 81 + 256) - 3 * (x * y * z - 3) := h9
    rw [h12] at h11
    nlinarith

  exact h10