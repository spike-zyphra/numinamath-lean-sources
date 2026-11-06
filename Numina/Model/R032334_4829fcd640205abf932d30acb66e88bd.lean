import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_54003 :
  IsLeast {n | ∃ x y z : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ 4 ∧ n = |x - y| + |y - z| ∧
  y^2 = x^2 + 2 ∧ z^2 = y^2 + 2} (2 * (2 - sqrt 3)) := by
  constructor
  · -- Show that 2 * (2 - Real.sqrt 3) is in the set.
    use 2 * Real.sqrt 3
    use Real.sqrt 14
    use (4 : ℝ)
    have h1 : 0 ≤ 2 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3]
    have h2 : Real.sqrt 14 ≥ 2 * Real.sqrt 3 := by
      have h3 : (Real.sqrt 14 : ℝ) ^ 2 ≥ (2 * Real.sqrt 3 : ℝ) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h4 : Real.sqrt 14 ≥ 0 := by positivity
      have h5 : 2 * Real.sqrt 3 ≥ 0 := by nlinarith [Real.sqrt_nonneg 3]
      nlinarith [sq_nonneg (Real.sqrt 14 - 2 * Real.sqrt 3), Real.sqrt_nonneg 14, Real.sqrt_nonneg 3, h3]
    have h3 : Real.sqrt 14 ≤ (4 : ℝ) := by
      have h4 : (Real.sqrt 14 : ℝ) ^ 2 ≤ (4 : ℝ) ^ 2 := by
        nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)]
      have h5 : Real.sqrt 14 ≥ 0 := by positivity
      nlinarith
    constructor
    · -- Show 0 ≤ x
      linarith
    constructor
    · -- Show x ≤ y
      linarith [h1, h2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 14]
    constructor
    · -- Show y ≤ z
      linarith [h2, h3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 14]
    constructor
    · -- Show z ≤ 4
      linarith [h3]
    constructor
    · -- Show n = |x - y| + |y - z|
      have h4 : 2 * (2 - Real.sqrt 3) = |(2 * Real.sqrt 3 : ℝ) - Real.sqrt 14| + |Real.sqrt 14 - (4 : ℝ)| := by
        have h5 : |(2 * Real.sqrt 3 : ℝ) - Real.sqrt 14| = Real.sqrt 14 - 2 * Real.sqrt 3 := by
          rw [abs_of_nonpos]
          nlinarith
          all_goals nlinarith
        have h6 : |Real.sqrt 14 - (4 : ℝ)| = (4 : ℝ) - Real.sqrt 14 := by
          rw [abs_of_nonpos]
          nlinarith
          all_goals nlinarith
        linarith [h5, h6]
      linarith [h4]
    constructor
    · -- Show y^2 = x^2 + 2
      nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Show z^2 = y^2 + 2
      nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · -- Show that 2 * (2 - Real.sqrt 3) is the minimum
    intro n hn
    rcases hn with ⟨x, y, z, hx0, hxy1, hyz1, hz4, hn, hy2, hz2⟩
    have h3 : |x - y| + |y - z| ≥ 2 * (2 - Real.sqrt 3) := by
      have h4 : |x - y| = y - x := by
        rw [abs_of_nonpos]
        nlinarith
        all_goals linarith
      have h5 : |y - z| = z - y := by
        rw [abs_of_nonpos]
        nlinarith
        all_goals linarith
      have h6 : |x - y| + |y - z| = z - x := by
        linarith [h4, h5]
      have h7 : z ^ 2 - x ^ 2 = 4 := by
        nlinarith
      have h8 : z - x ≥ 0 := by nlinarith
      have h9 : z + x > 0 := by nlinarith
      have h10 : z - x ≥ 4 - 2 * Real.sqrt 3 := by
        nlinarith [sq_nonneg (z - 4), sq_nonneg (x - 2 * Real.sqrt 3), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (z ^ 2 - 16), sq_nonneg (x ^ 2 - 12)]
      linarith
    have h4 : n = |x - y| + |y - z| := by
      linarith [hn]
    linarith [h3, h4]