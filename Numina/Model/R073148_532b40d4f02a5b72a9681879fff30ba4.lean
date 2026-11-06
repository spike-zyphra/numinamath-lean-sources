import Mathlib

open Real Set

theorem algebra_6833 (x : ℝ) :
    IsGreatest {y | ∃ x : ℝ, y = 1 / sqrt (x ^ 2 + 14 * x + 99)} (Real.sqrt 2 / 10) := by
  constructor
  · -- Show that √2 / 10 is in the set with x = -7
    use -7
    have h1 : sqrt ( (-7 : ℝ) ^ 2 + 14 * (-7 ) + 99 ) = Real.sqrt 50 := by norm_num
    rw [h1]
    have h2 : Real.sqrt (50 : ℝ) = Real.sqrt (5 ^ 2 * (2 : ℝ)) := by norm_num
    have h3 : Real.sqrt (5 ^ 2 * (2 : ℝ)) = Real.sqrt (5 ^ 2) * Real.sqrt (2 : ℝ) := by
      rw [Real.sqrt_mul]
      all_goals
        norm_num
    have h4 : Real.sqrt ((5 : ℝ) ^ 2) = (5 : ℝ) := by
      rw [Real.sqrt_sq_eq_abs]
      norm_num
    rw [h2, h3, h4]
    field_simp
    <;> ring_nf
    <;> norm_num [Real.sqrt_sq]
    all_goals
      ring_nf
      <;> norm_num
  · -- Show that √2 / 10 is the greatest element in the set
    rintro y ⟨x, hx⟩
    have h2 : x ^ 2 + 14 * x + 99 ≥ 50 := by
      nlinarith [sq_nonneg (x + 7)]
    have h3 : sqrt (x ^ 2 + 14 * x + 99 ) ≥ sqrt (50 : ℝ) := by
      apply Real.sqrt_le_sqrt (by linarith)
    have h50 : sqrt (50 : ℝ) = 5 * Real.sqrt (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h4 : (1 : ℝ) / sqrt (x ^ 2 + 14 * x + 99 ) ≤ (1 : ℝ) / sqrt (50 : ℝ) := by
      apply one_div_le_one_div_of_le
      all_goals
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (50 : ℝ) by norm_num : (50 : ℝ) > 0), h3]
    have h5 : (1 : ℝ) / sqrt (50 : ℝ) = Real.sqrt (2 : ℝ) / 10 := by
      have h51 : sqrt (50 : ℝ) = 5 * Real.sqrt (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h51]
      field_simp
      <;> ring_nf
      <;> norm_num [Real.sqrt_sq]
    have h500 : Real.sqrt 2 / 10 > 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
    linarith [show y ≤ (Real.sqrt 2 / 10 : ℝ) by 
      rw [hx]
      linarith [h4, h5]
    ]