import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_600043 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a + b = 1 ∧ x = 1 / (2 * a) + 1 / b} (3 / 2 + sqrt 2) := by
  constructor
  · -- Show that $3/2 + \sqrt{2}$ is in the set
    use Real.sqrt 2 - 1
    use 2 - Real.sqrt 2
    constructor
    · -- Show that sqrt 2 - 1 > 0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    constructor
    · -- Show that 2 - sqrt 2 > 0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    constructor
    · -- Show that (sqrt 2 - 1) + (2 - sqrt 2) = 1
      ring_nf
    · -- Show that 3 / 2 + sqrt 2 = 1 / (2 * (sqrt 2 - 1)) + 1 / (2 - sqrt 2)
      have h1 : Real.sqrt 2 > 0 := by positivity
      have h2 : (Real.sqrt 2 - 1 : ℝ) > 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h3 : (2 - Real.sqrt 2 : ℝ) > 0 := by nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      field_simp [show (2 * (Real.sqrt 2 - 1) : ℝ) ≠ 0 by nlinarith, show (2 - Real.sqrt 2 : ℝ) ≠ 0 by nlinarith]
      <;> ring_nf <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 1)]
  · -- Show that $3/2 + \sqrt{2}$ is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h_eq, heq⟩
    have h1 : b = 1 - a := by linarith
    rw [h1] at heq
    have h2 : a > 0 := by linarith
    have h3 : 1 - a > 0 := by nlinarith
    have h4 : 1 / (2 * a) + 1 / (1 - a) ≥ 3 / 2 + Real.sqrt 2 := by
      have h5 : 0 < a := by linarith
      have h6 : 0 < 1 - a := by nlinarith
      have h7 : 0 < 2 * a * (1 - a) := by positivity
      have h8 : (1 / (2 * a) + 1 / (1 - a) ) - (3 / 2 + Real.sqrt 2) ≥ 0 := by
        have h9 : (1 / (2 * a) + 1 / (1 - a) ) - (3 / 2 + Real.sqrt 2) = ( (1 - a) + 2 * a - (3 + 2 * Real.sqrt 2) * (a * (1 - a)) ) / (2 * a * (1 - a)) := by
          field_simp
          <;> ring_nf <;> field_simp
          <;> ring
        rw [h9] at *
        apply div_nonneg
        nlinarith [ sq_nonneg (a - (Real.sqrt 2 - 1)), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (a - (2 - Real.sqrt 2)), mul_pos (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num), sq_nonneg (a - 1 / 2), Real.sqrt_nonneg 2, sq_nonneg (a * (1 - a)), mul_pos (show 0 < (a : ℝ) by linarith) (show 0 < (1 - a : ℝ) by nlinarith) ]
        all_goals
          positivity
      nlinarith
    nlinarith [heq, h4]