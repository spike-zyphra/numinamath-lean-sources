import Mathlib

theorem algebra_300760 {x : ℝ} (hx : x = (1 + Real.sqrt 1994) / 2) :
    (4 * x^3 - 1997 * x - 1994) ^ 2001 = -1 := by
  have h1 : x = (1 + Real.sqrt 1994) / 2 := hx
  have eq1 : 4 * x^3 - 1997 * x - 1994 = -1 := by
    rw [h1]
    ring_nf
    have h2 : Real.sqrt 1994 ^ 2 = 1994 := by
      exact Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (1994 : ℝ) by norm_num : (0 : ℝ) < (1994 : ℝ)),
      Real.sq_sqrt (show (0 : ℝ) ≤ (1994 : ℝ) by norm_num : (0 : ℝ) ≤ (1994 : ℝ)),
      pow_two_nonneg (Real.sqrt 1994 - 1),
      Real.sq_sqrt (show (0 : ℝ) ≤ (1994 : ℝ) by norm_num : (0 : ℝ) ≤ (1994 : ℝ))]
  rw [eq1]
  norm_num