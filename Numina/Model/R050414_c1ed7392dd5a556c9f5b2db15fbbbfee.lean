import Mathlib

theorem algebra_305940 {x : ℝ} (hx : x = 3) :
    Real.arctan (1 / 2) = Real.arctan (1 / x) + Real.arctan (1 / 7) := by
  rw [hx]
  have h1 : Real.arctan (1 / 3) + Real.arctan (1 / 7) = Real.arctan (1 / 2) := by
    have h : Real.arctan (1 / 3) + Real.arctan (1 / 7) = Real.arctan ((1 / 3 + 1 / 7) / (1 - (1 / 3) * (1 / 7)))
      := by
      rw [Real.arctan_add]
      all_goals norm_num
    have h2 : (1 / 3 + 1 / 7 : ℝ) / (1 - (1 / 3) * (1 / 7)) = (1 / 2 : ℝ) := by
      norm_num
    rw [h2] at h
    linarith [h]
  linarith [h1]