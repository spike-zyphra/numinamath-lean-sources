import Mathlib

theorem algebra_326993 (a : ℝ) (f : ℝ → ℝ)
    (hf : ∀ x, f x = x ^ 2 - 2 * x - abs (x - 1 - a) - abs (x - 2) + 4)
    (ha : ∀ x, f x ≥ 0) :
    a ≤ 1 := by
  have h1 := ha 0
  have h2 : f 0 ≥ 0 := h1
  have h3 : f 0 = 0 ^ 2 - 2 * 0 - abs (0 - 1 - a) - abs (0 - 2) + 4 := hf 0
  rw [h3] at h2
  have h4 : abs (0 - 1 - a : ℝ) = abs (-1 - a : ℝ) := by
    have : (0 - 1 - a : ℝ) = -1 - a := by ring
    rw [this]
  have h5 : abs (0 - 2 : ℝ) = (2 : ℝ) := by
    norm_num [abs_of_nonneg, abs_of_neg]
  rw [h4, h5] at h2
  have h6 : abs (-1 - a) ≤ 2 := by
    linarith
  have h7 : -2 ≤ -1 - a := by
    linarith [abs_le.mp h6]
  linarith