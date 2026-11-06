import Mathlib

open Real

theorem inequalities_599496 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    3 + 2 * √2 ≤ 1 / x + 2 / y := by

  have h1 : y = 1 - x := by linarith

  rw [h1]

  have h2 : 0 < (1 - x) := by
    nlinarith [hxy, hx, hy]

  have h3 : 1 / x + 2 / (1 - x) - (3 + 2 * Real.sqrt 2) ≥ 0 := by
    have h4 : 0 < x * (1 - x) := by
      positivity
    -- = 0
    have h5 : 1 / x + 2 / (1 - x) - (3 + 2 * Real.sqrt 2) =
      ( (1 - x) + 2 * x - (3 + 2 * Real.sqrt 2) * x * (1 - x) ) / (x * (1 - x)) := by
      field_simp [(show 0 < x by assumption), (show 0 < 1 - x by assumption)]
      ring
    rw [h5]
    have h6 : ( (1 - x) + 2 * x - (3 + 2 * Real.sqrt 2) * x * (1 - x) ) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith), sq_nonneg (x - (-1 + Real.sqrt 2)), sq_nonneg (x - (2 - Real.sqrt 2)), sq_nonneg (Real.sqrt 2 - 1), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
    have h7 : (x * (1 - x)) > 0 := by
      positivity
    apply div_nonneg h6 (by positivity)

  linarith [show 1 / x + 2 / (1 - x) ≥ 3 + 2 * Real.sqrt 2 by linarith [h3]]