import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327148 {f g : ℝ → ℝ}
  (hg : ∀ x, g x = tan (x / 2)) (hfg : ∀ x, f (g x) = sin (2 * x)) :
  f (Real.sqrt 2 / 2) = 4 * Real.sqrt 2 / 9 := by
  have h3 : g (2 * arctan (Real.sqrt 2 / 2)) = Real.sqrt 2 / 2 := by
    have h4 : g (2 * arctan (Real.sqrt 2 / 2)) = tan ( (2 * arctan (Real.sqrt 2 / 2) ) / 2 ) := by
      apply hg
    rw [h4]
    have h5 : ( (2 * arctan (Real.sqrt 2 / 2) ) / 2 ) = arctan (Real.sqrt 2 / 2) := by
      ring
    rw [h5]
    rw [Real.tan_arctan]
  have h4 : f (g (2 * arctan (Real.sqrt 2 / 2))) = sin (2 * (2 * arctan (Real.sqrt 2 / 2)) ) := by
    apply hfg
  rw [h3] at h4
  have h5 : 2 * (2 * arctan (Real.sqrt 2 / 2)) = 4 * arctan (Real.sqrt 2 / 2) := by ring
  rw [h5] at h4
  have h6 : sin (4 * arctan (Real.sqrt 2 / 2) ) = 4 * Real.sqrt 2 / 9 := by
    have h7 : sin (4 * arctan (Real.sqrt 2 / 2) ) = 2 * sin (2 * arctan (Real.sqrt 2 / 2) ) * cos (2 * arctan (Real.sqrt 2 / 2) ) := by
      rw [show 4 * arctan (Real.sqrt 2 / 2) = 2 * (2 * arctan (Real.sqrt 2 / 2) ) by ring]
      rw [sin_two_mul]
    have h8 : sin (2 * arctan (Real.sqrt 2 / 2) ) = 2 * Real.sqrt 2 / 3 := by
      have h9 : sin (2 * arctan (Real.sqrt 2 / 2) ) = 2 * sin (arctan (Real.sqrt 2 / 2) ) * cos (arctan (Real.sqrt 2 / 2) ) := by
        rw [sin_two_mul]
      have h10 : sin (arctan (Real.sqrt 2 / 2) ) = Real.sqrt 2 / 2 / Real.sqrt (1 + (Real.sqrt 2 / 2) ^ 2 ) := by
        rw [Real.sin_arctan]
      have h11 : cos (arctan (Real.sqrt 2 / 2) ) = 1 / Real.sqrt (1 + (Real.sqrt 2 / 2) ^ 2 ) := by
        rw [Real.cos_arctan]
      have h12 : (1 + (Real.sqrt 2 / 2 ) ^ 2 : ℝ ) = (3 / 2 : ℝ ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h13 : Real.sqrt (1 + (Real.sqrt 2 / 2 ) ^ 2 ) = Real.sqrt (3 / 2 ) := by
        rw [h12]
      have h14 : Real.sqrt (3 / 2 : ℝ ) = Real.sqrt 3 / Real.sqrt 2 := by
        rw [Real.sqrt_div (by norm_num)]
      rw [h9]
      rw [h10, h11, h13, h14]
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    have h9 : cos (2 * arctan (Real.sqrt 2 / 2) ) = 1 / 3 := by
      have h10 : cos (2 * arctan (Real.sqrt 2 / 2) ) = 2 * (cos (arctan (Real.sqrt 2 / 2) ) ) ^ 2 - 1 := by
        rw [cos_two_mul]
      have h11 : cos (arctan (Real.sqrt 2 / 2) ) = 1 / Real.sqrt (1 + (Real.sqrt 2 / 2 ) ^ 2 ) := by
        rw [Real.cos_arctan]
      have h12 : (1 + (Real.sqrt 2 / 2 ) ^ 2 : ℝ ) = (3 / 2 : ℝ ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h13 : Real.sqrt (1 + (Real.sqrt 2 / 2 ) ^ 2 ) = Real.sqrt (3 / 2 ) := by
        rw [h12]
      have h14 : Real.sqrt (3 / 2 : ℝ ) = Real.sqrt 3 / Real.sqrt 2 := by
        rw [Real.sqrt_div (by norm_num)]
      rw [h10, h11, h13, h14]
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    rw [h7, h8, h9]
    all_goals
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3)]
  rw [h4]
  exact h6