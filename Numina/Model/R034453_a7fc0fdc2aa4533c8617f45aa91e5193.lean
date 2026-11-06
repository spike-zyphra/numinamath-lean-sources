import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_205261 {f : ℝ → ℝ} (hf : f = λ x => (x^2 - 2 * x + 3) / (x^2 + 2 * x + 3)) :
    IsGreatest (range f) (2 + sqrt 3) ∧ IsLeast (range f) (2 - sqrt 3) := by
  constructor
  · -- Show that 2 + sqrt 3 is the greatest element in the range
    constructor
    · -- Show 2 + sqrt 3 is in the range
      use -Real.sqrt 3
      rw [hf]
      have h3 : (-Real.sqrt 3 : ℝ) ^ 2 - 2 * (-Real.sqrt 3) + 3 = 6 + 2 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
      have h4 : (-Real.sqrt 3 : ℝ) ^ 2 + 2 * (-Real.sqrt 3) + 3 = 6 - 2 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
      simp only [h3, h4]
      have h5 : (6 - 2 * Real.sqrt 3 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
      field_simp [h5]
      <;> ring_nf <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
    · -- Show that 2 + sqrt 3 is indeed the greatest
      intro y
      rintro ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have h2 : x^2 + 2 * x + 3 > 0 := by
        nlinarith [sq_nonneg (x + 1)]
      have h3 : (x^2 - 2 * x + 3) / (x^2 + 2 * x + 3) ≤ (2 + Real.sqrt 3) := by
        have h4 : (x^2 + 2 * x + 3) > 0 := by
          nlinarith [sq_nonneg (x + 1)]
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), sq_nonneg (x + Real.sqrt 3), sq_nonneg (x), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), sq_nonneg (x + 1)]
      linarith [h3, hx]
  · -- Show that 2 - sqrt 3 is the least element in the range
    constructor
    · -- Show 2 - sqrt 3 is in the range
      use Real.sqrt 3
      rw [hf]
      have h3 : (Real.sqrt 3 : ℝ) ^ 2 - 2 * (Real.sqrt 3) + 3 = 6 - 2 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
      have h4 : (Real.sqrt 3 : ℝ) ^ 2 + 2 * (Real.sqrt 3) + 3 = 6 + 2 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
      simp only [h3, h4]
      have h5 : (6 + 2 * Real.sqrt 3 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
      field_simp [h5]
      <;> ring_nf <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
    · -- Show that 2 - sqrt 3 is indeed the least
      intro y
      rintro ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have h2 : x^2 + 2 * x + 3 > 0 := by
        nlinarith [sq_nonneg (x + 1)]
      have h3 : (x^2 - 2 * x + 3) / (x^2 + 2 * x + 3) ≥ (2 - Real.sqrt 3) := by
        have h4 : (x^2 + 2 * x + 3) > 0 := by
          nlinarith [sq_nonneg (x + 1)]
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), sq_nonneg (x - Real.sqrt 3), sq_nonneg (x), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), sq_nonneg (x + 1)]
      linarith [h3, hx]