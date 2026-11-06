import Mathlib

theorem algebra_114757 (M : ℝ) (hM : ∀ x y z u : ℝ, x > 0 → y > 0 → z > 0 → u > 0 → z ≥ y → x - 2 * y = z - 2 * u → 2 * y * z = u * x → M ≤ z / y) :
    M ≤ 6 + 4 * Real.sqrt 2 := by
  have h1 := hM (4 + 2 * Real.sqrt 2) 1 (6 + 4 * Real.sqrt 2) (2 + Real.sqrt 2) (by positivity) (by positivity) (by positivity) (by positivity) (by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (0 : ℝ) < 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
  ) (by
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (0 : ℝ) < 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
  ) (by
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (0 : ℝ) < 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
  )
  have h2 : M ≤ (6 + 4 * Real.sqrt 2 : ℝ) := by
    norm_num at h1 ⊢
    linarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
  linarith