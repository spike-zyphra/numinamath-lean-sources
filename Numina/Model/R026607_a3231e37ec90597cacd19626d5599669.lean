import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_193356 (p q : ℝ) :
  (∀ x ∈ Icc 0 1, |sqrt (1 - x^2) - p * x - q| ≤ (sqrt 2 - 1) / 2) ↔
  (p, q) = (-1, (sqrt 2 + 1) / 2) := by
  constructor
  · -- Forward direction
    intro h
    have h1 := h (Real.sqrt 2 / 2) (by
      constructor
      · -- Show sqrt 2 / 2 ≥ 0
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · -- Show sqrt 2 / 2 ≤ 1
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    )
    have h2 := h 0 (by simp)
    have h3 := h 1 (by norm_num)
    have h4 : sqrt (1 - (Real.sqrt 2 / 2) ^ 2) = Real.sqrt 2 / 2 := by
      have h5 : (Real.sqrt 2 / 2: ℝ) ^ 2 = 1 / 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [h5]
      have h6 : sqrt (1 - (1 / 2 : ℝ)) = sqrt (1 / 2 : ℝ) := by ring_nf
      rw [h6]
      have h7 : sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h7]
    rw [h4] at h1
    have eq1 : -(sqrt 2 - 1) / 2 ≤ Real.sqrt 2 / 2 - p * (Real.sqrt 2 / 2) - q := by 
      linarith [abs_le.mp h1]
    have eq2 : Real.sqrt 2 / 2 - p * (Real.sqrt 2 / 2) - q ≤ (sqrt 2 - 1) / 2 := by 
      linarith [abs_le.mp h1]

    have eq3 : - (sqrt 2 - 1) / 2 ≤ (1 - q) := by
      have h51 : |sqrt (1 - (0: ℝ) ^2) - p * (0: ℝ) - q| ≤ (sqrt 2 - 1) / 2 := h2
      have eq6 : sqrt (1 - (0: ℝ) ^2) = (1 : ℝ) := by
        simp
      rw [eq6] at h51
      cases' abs_le.mp h51 with h52 h53
      linarith

    have eq4 : (1 - q) ≤ (sqrt 2 - 1) / 2 := by
      have h51 : |sqrt (1 - (0: ℝ) ^2) - p * (0: ℝ) - q| ≤ (sqrt 2 - 1) / 2 := h2
      have eq6 : sqrt (1 - (0: ℝ) ^2) = (1 : ℝ) := by
        simp
      rw [eq6] at h51
      cases' abs_le.mp h51 with h52 h53
      linarith

    have eq5 : - (sqrt 2 - 1) / 2 ≤ -p - q := by
      have h51 : |sqrt (1 - (1: ℝ) ^2) - p * (1: ℝ) - q| ≤ (sqrt 2 - 1) / 2 := h3
      have eq6 : sqrt (1 - (1: ℝ) ^2) = (0 : ℝ) := by 
        simp [sqrt_zero]
      rw [eq6] at h51
      cases' abs_le.mp h51 with h52 h53
      linarith

    have eq6 : -p - q ≤ (sqrt 2 - 1) / 2 := by 
      have h51 : |sqrt (1 - (1: ℝ) ^2) - p * (1: ℝ) - q| ≤ (sqrt 2 - 1) / 2 := h3
      have eq6 : sqrt (1 - (1: ℝ) ^2) = (0 : ℝ) := by 
        simp [sqrt_zero]
      rw [eq6] at h51
      cases' abs_le.mp h51 with h52 h53
      linarith

    have hp1 : p = -1 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (p + 1), sq_nonneg (q - (sqrt 2 + 1)/2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    
    have hq1 : q = (sqrt 2 + 1) / 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (q - (sqrt 2 + 1)/2), Real.sq_sqrt (show (0 : ℝ) ≤ (2: ℝ) by norm_num), hp1, mul_nonneg (show 0 ≤ (sqrt 2 : ℝ) by positivity) (show 0 ≤ (sqrt 2 : ℝ) by positivity)]
    
    simp [Prod.ext_iff, hp1, hq1]
  · -- Backward direction
    rintro ⟨rfl, rfl⟩
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    have h7 : - (sqrt 2 - 1) / 2 ≤ sqrt (1 - x ^ 2) - (-1 : ℝ) * x - (sqrt 2 + 1) / 2 := by
      have h10 : sqrt (1 - x ^ 2) + x - (sqrt 2 + 1) / 2 ≥ - (sqrt 2 - 1) / 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (1 - x^2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x - Real.sqrt 2 / 2), sq_nonneg (sqrt (1 - x^2) - Real.sqrt 2 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x ^ 2 : ℝ) by nlinarith), Real.sqrt_nonneg (1 - x ^ 2), mul_nonneg (Real.sqrt_nonneg (1 - x^2)) (Real.sqrt_nonneg (2)), sq_nonneg (x - Real.sqrt 2 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      nlinarith
    have h8 : sqrt (1 - x ^ 2) - (-1 : ℝ) * x - (sqrt 2 + 1) / 2 ≤ (sqrt 2 - 1) / 2 := by
      have h11 : sqrt (1 - x ^ 2) + x - (sqrt 2 + 1) / 2 ≤ (sqrt 2 - 1) / 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (1 - x^2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x - Real.sqrt 2 / 2), sq_nonneg (sqrt (1 - x^2) - Real.sqrt 2 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x ^ 2 : ℝ) by nlinarith), Real.sqrt_nonneg (1 - x ^ 2), mul_nonneg (Real.sqrt_nonneg (1 - x^2)) (Real.sqrt_nonneg (2)), sq_nonneg (x - Real.sqrt 2 / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      nlinarith
    rw [show |sqrt (1 - x^2) - (-1 : ℝ) * x - (sqrt 2 + 1 : ℝ) / 2| = |sqrt (1 - x^2) + x - (sqrt 2 + 1 : ℝ) / 2| by ring_nf]
    apply abs_le.mpr
    constructor <;> nlinarith [h7, h8]