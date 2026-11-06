import Mathlib

theorem algebra_298525 {f : ℝ → ℝ} (h : ∀ x, f (x ^ 2 + x) + 2 * f (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x) :
    f 50 = 146 := by
  have eq1 := h ((-1 + Real.sqrt 201) / 2)
  have eq2 := h ((-1 - Real.sqrt 201) / 2)
  have eq3 := h ((3 + Real.sqrt 201) / 2)
  have eq4 := h ((3 - Real.sqrt 201) / 2)
  have h1 : ((-1 + Real.sqrt 201) / 2 : ℝ) ^ 2 + ((-1 + Real.sqrt 201) / 2 : ℝ) = (50 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 201, Real.sq_sqrt (show 0 ≤ (201 : ℝ) by norm_num)]
  have h2 : ((-1 - Real.sqrt 201) / 2 : ℝ) ^ 2 + ((-1 - Real.sqrt 201) / 2 : ℝ) = (50 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 201, Real.sq_sqrt (show 0 ≤ (201 : ℝ) by norm_num)]
  have h3 : ((3 + Real.sqrt 201) / 2 : ℝ) ^ 2 - 3 * ((3 + Real.sqrt 201) / 2 : ℝ) + 2 = (50 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 201, Real.sq_sqrt (show 0 ≤ (201 : ℝ) by norm_num)]
  have h4 : ((3 - Real.sqrt 201) / 2 : ℝ) ^ 2 - 3 * ((3 - Real.sqrt 201) / 2 : ℝ) + 2 = (50 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 201, Real.sq_sqrt (show 0 ≤ (201 : ℝ) by norm_num)]
  norm_num [h1, h2, h3, h4] at eq1 eq2 eq3 eq4
  ring_nf at eq1 eq2 eq3 eq4 ⊢
  nlinarith [Real.sqrt_nonneg 201, Real.sq_sqrt (show 0 ≤ (201 : ℝ) by norm_num)]