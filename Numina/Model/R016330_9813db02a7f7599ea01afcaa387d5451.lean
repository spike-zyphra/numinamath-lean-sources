import Mathlib

open Real

theorem algebra_10636 {a b : ℝ} (ha : a > b) (hab : a * b = 1) :
    IsLeast {x | ∃ a b : ℝ, a > b ∧ a * b = 1 ∧ x = (a ^ 2 + b ^ 2) / (a - b)} (2 * sqrt 2) := by
  constructor
  · -- Show that 2 * sqrt 2 is in the set
    use (Real.sqrt 2 + Real.sqrt 6) / 2, ( - Real.sqrt 2 + Real.sqrt 6) / 2
    constructor
    · -- Show a > b
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 6]
    constructor
    · -- Show a * b = 1
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)), sq_nonneg (Real.sqrt 2 - Real.sqrt 6)]
    · -- Show (a ^ 2 + b ^ 2) / (a - b) = 2 * sqrt 2
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
      have h4 : ((Real.sqrt 2 + Real.sqrt 6) / 2 : ℝ) ^ 2 + (( - Real.sqrt 2 + Real.sqrt 6) / 2 : ℝ) ^ 2 = 4 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h1, h2, sq_nonneg (Real.sqrt 2 * Real.sqrt 6), sq_nonneg (Real.sqrt 2 - Real.sqrt 6)]
      have h5 : ((Real.sqrt 2 + Real.sqrt 6) / 2 : ℝ) - (( - Real.sqrt 2 + Real.sqrt 6) / 2 : ℝ) = Real.sqrt 2 := by
        ring
      rw [h4, h5]
      field_simp
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
  · -- Show that 2 * sqrt 2 is the least element
    intro x hx
    rcases hx with ⟨a, b, ha, hab, hx⟩
    have h1 : a - b > 0 := by linarith
    have h2 : a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 := by
      nlinarith [hab, sq_pos_of_pos (show 0 < a - b by linarith)]
    have h3 : (a ^ 2 + b ^ 2) / (a - b) = (a - b) + 2 / (a - b) := by
      rw [h2]
      have h4 : a - b ≠ 0 := by linarith
      field_simp
      <;> ring
    have h4 : (a - b) + 2 / (a - b) ≥ 2 * Real.sqrt 2 := by
      have h5 : (a - b) * (2 / (a - b)) = 2 := by
        field_simp [show a - b ≠ 0 by linarith]
        <;> nlinarith
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((a - b) - Real.sqrt 2), sq_nonneg ((a - b) * (a - b) - 2), mul_pos (show 0 < a - b by linarith) (show 0 < a - b by linarith)]
    have h8 : (a ^ 2 + b ^ 2) / (a - b) ≥ 2 * Real.sqrt 2 := by
      rw [h3]
      linarith [h4]
    rw [hx] at *
    linarith [h8]