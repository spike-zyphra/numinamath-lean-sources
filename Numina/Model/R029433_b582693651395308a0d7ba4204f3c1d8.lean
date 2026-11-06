import Mathlib

theorem algebra_313096 (f : ℝ → ℝ) (a : ℝ) (hf : ∀ x ∈ Set.Ioo 0 1, f x * f (1 - x) ≥ 1)
    (h : ∀ x, f x = a / x - x) :
    a ≤ -1 / 4 ∨ a ≥ 1 := by
  have h1 := hf (1 / 2) (by norm_num)
  rw [show 1 - (1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num] at h1
  have h2 : f (1 / 2) = 2 * a - 1 / 2 := by
    rw [h]
    field_simp
    <;> ring
  rw [h2] at h1
  have h3 := hf (1 / 4) (by norm_num)
  have h4 : f (1 / 4) = 4 * a - 1 / 4 := by
    rw [h]
    field_simp
    <;> ring
  have h5 : f (1 - (1 / 4 : ℝ)) = (4 * a / 3) - 3 / 4 := by
    have h6 : (1 - (1 / 4 : ℝ) ) = (3 / 4 : ℝ) := by norm_num
    rw [h6]
    rw [h]
    field_simp
    <;> ring
  rw [h4, h5] at h3
  by_cases h5 : a ≤ -1 / 4
  · left
    exact h5
  · -- Assume that a > -1/4, prove a ≥ 1
    have h6 : a > -1 / 4 := by linarith
    right
    by_contra h7
    push_neg at h7
    have h8 : a > 0 := by nlinarith
    have h9 : a < 1 := by nlinarith
    have h3 := hf (Real.sqrt a) (show Real.sqrt a ∈ Set.Ioo (0 : ℝ) 1 by
      constructor
      · -- Show sqrt a > 0
        apply Real.sqrt_pos.mpr
        nlinarith
      · -- Show sqrt a < 1
        nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), h9]
    )
    have h6 : f (Real.sqrt a) = 0 := by
      rw [h]
      have h7 : Real.sqrt a > 0 := by
        apply Real.sqrt_pos.mpr
        nlinarith
      field_simp [h7]
      <;> nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith)]
    rw [h6] at h3
    norm_num at h3
    all_goals nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith)]