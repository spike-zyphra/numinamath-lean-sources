import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_126767 {x y : ℝ} (hx : x > 0) (hy : y > 0) (hxy : x > y)
  (hxy1 : y * x = 1) :
  IsLeast {z | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x > y ∧ y * x = 1 ∧ z = (x ^ 2 + y ^ 2) / (x - y)} (2 * sqrt 2) := by
  constructor
  · -- Show that 2 * sqrt 2 is in the set.
    use (√6 + √2) / 2, (√6 - √2) / 2
    constructor
    · -- Show x > 0
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    constructor
    · -- Show y > 0
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    constructor
    · -- Show x > y
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    constructor
    · -- Show y * x = 1
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show 2 * sqrt 2 = (x ^ 2 + y ^ 2) / (x - y)
      have h1 : ((√6 + √2) / 2 : ℝ) ^ 2 + ((√6 - √2) / 2 : ℝ) ^ 2 = 4 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 2)]
      have h2 : ((√6 + √2) / 2 : ℝ) - ((√6 - √2) / 2 : ℝ) = Real.sqrt 2 := by
        ring_nf
      have eq1 : (( (√6 + √2) / 2 : ℝ) ^ 2 + ((√6 - √2) / 2 : ℝ) ^ 2 ) / (( (√6 + √2) / 2 : ℝ ) - ((√6 - √2) / 2 : ℝ )) = 2 * Real.sqrt 2 := by
        rw [h1, h2]
        have h3 : Real.sqrt 2 > 0 := by positivity
        field_simp
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      linarith [eq1, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
  · -- Show that 2 * sqrt 2 is the least element in the set
    intro z hz
    rcases hz with ⟨x, y, hx, hy, hxy, hxy1, hz⟩
    have h3 : (x ^ 2 + y ^ 2) / (x - y) ≥ 2 * Real.sqrt 2 := by
      have h4 : x - y > 0 := by linarith
      have h6 : x ^ 2 + y ^ 2 ≥ 2 * Real.sqrt 2 * (x - y) := by
        nlinarith [sq_nonneg (x - y - Real.sqrt 2), sq_nonneg (x + y - Real.sqrt 6), sq_nonneg (x * y - 1), Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (x - ((√6 + √2) / 2)), sq_nonneg (y - ((√6 - √2) / 2)), mul_pos hx hy, Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, sq_nonneg (x - 2 * y), sq_nonneg (x * y - 1)]
      have h7 : (x ^ 2 + y ^ 2) / (x - y) ≥ 2 * Real.sqrt 2 := by
        have h8 : x - y > 0 := by linarith
        apply (le_div_iff₀ h8).mpr
        linarith
      linarith
    linarith [hz, h3]