import Mathlib

theorem algebra_100669 {f : ℝ → ℝ} (h : ∀ x, f (x ^ 2 + x) + 2 * f (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x) :
    f 2011 = 6029 := by
  have h1 := h ((-1 + Real.sqrt 8045) / 2)
  have h2 := h ((3 + Real.sqrt 8045) / 2)
  have h3 := h ((-1 - Real.sqrt 8045) / 2)
  have h4 := h ((3 - Real.sqrt 8045) / 2)
  ring_nf at h1 h2 h3 h4
  norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ (8045 : ℝ) by norm_num : (0 : ℝ) ≤ (8045 : ℝ)), pow_two] at h1 h2 h3 h4
  nlinarith [Real.sqrt_pos.mpr (show (8045 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (8045 : ℝ) by norm_num : (0 : ℝ) ≤ (8045 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (8045 : ℝ) by norm_num : (0 : ℝ) ≤ (8045 : ℝ))]