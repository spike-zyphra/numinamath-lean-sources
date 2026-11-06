import Mathlib

open Real Set
open scoped Real

theorem algebra_10638 {x y : ℝ} (h : cos x + cos y = 1) :
    sin x - sin y ∈ Icc (-sqrt 3) (sqrt 3) := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : sin y ^ 2 + cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y

  have h3 : (cos x + cos y) ^ 2 = 1 := by
    rw [h]
    norm_num
  
  have h4 : cos x ^ 2 + cos y ^ 2 + 2 * (cos x * cos y) = 1 := by 
    nlinarith

  have h5 : (sin x - sin y) ^ 2 = sin x ^ 2 + sin y ^ 2 - 2 * (sin x * sin y) := by
    ring
  
  have h6 : sin x ^ 2 + sin y ^ 2 = 2 - (cos x ^ 2 + cos y ^ 2) := by
    have h8 : sin x ^ 2 + cos x ^ 2 = 1 := h1
    have h9 : sin y ^ 2 + cos y ^ 2 = 1 := h2
    nlinarith
  
  have h7 : cos x ^ 2 + cos y ^ 2 = 1 - 2 * (cos x * cos y) := by 
    nlinarith
  
  have hsin2 : (sin x - sin y) ^ 2 = 1 + 2 * (cos x * cos y - sin x * sin y) := by
    nlinarith [h5, h6, h7]

  have hcos : cos x * cos y - sin x * sin y = cos (x + y) := by
    rw [Real.cos_add]
  
  have hsin2_le : (sin x - sin y) ^ 2 ≤ 3 := by
    have hcos_le : -1 ≤ cos (x + y) ∧ cos (x + y) ≤ 1 := by
      constructor
      · linarith [Real.neg_one_le_cos (x + y)]
      · linarith [Real.cos_le_one (x + y)]
    nlinarith [hsin2, hcos_le, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  have h1_le : -sqrt 3 ≤ sin x - sin y := by
    have h2_le : (sin x - sin y) ^ 2 ≤ 3 := hsin2_le
    have h3_le : sin x - sin y ≥ -Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    linarith

  have h2_le : sin x - sin y ≤ sqrt 3 := by
    have h2_le : (sin x - sin y) ^ 2 ≤ 3 := hsin2_le
    have h3_le : sin x - sin y ≤ Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    linarith

  exact ⟨h1_le, h2_le⟩