import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_272331 :
  IsGreatest {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧
    a^2 + b^2 + c^2 + a * b + b * c + c * a ≤ 1 ∧ x = a + b + c} (Real.sqrt (3 / 2)) := by
  constructor
  · -- Show that sqrt(3/2) is in the set
    use 1 / Real.sqrt 6, 1 / Real.sqrt 6, 1 / Real.sqrt 6
    constructor
    · -- Show a > 0
      positivity
    constructor
    · -- Show b > 0
      positivity
    constructor
    · -- Show c > 0
      positivity
    constructor
    · -- Show the constraint is satisfied: a^2 + b^2 + c^2 + a * b + b * c + c * a ≤ 1
      have h1 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h2 : (1 / Real.sqrt 6 : ℝ) ^ 2 + (1 / Real.sqrt 6 : ℝ) ^ 2 + (1 / Real.sqrt 6 : ℝ) ^ 2 + (1 / Real.sqrt 6 : ℝ) * (1 / Real.sqrt 6 : ℝ) + (1 / Real.sqrt 6 : ℝ) * (1 / Real.sqrt 6 : ℝ) + (1 / Real.sqrt 6 : ℝ) * (1 / Real.sqrt 6 : ℝ) = 1 := by
        have h3 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := h1
        have h4 : (1 / Real.sqrt 6 : ℝ) ^ 2 = 1 / 6 := by
          field_simp [h3]
          <;> nlinarith
        have h5 : (1 / Real.sqrt 6 : ℝ) * (1 / Real.sqrt 6 : ℝ) = 1 / 6 := by
          have h6 : (Real.sqrt 6 : ℝ) * (Real.sqrt 6 : ℝ) = 6 := by
            nlinarith [h3]
          field_simp [h6]
          <;> nlinarith
        linarith [h4, h5]
      linarith [h2]
    · -- Show x = a + b + c
      have h1 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h2 : Real.sqrt (3 / 2) = Real.sqrt 6 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h2]
      have h3 : (1 / Real.sqrt 6 : ℝ) + (1 / Real.sqrt 6 : ℝ) + (1 / Real.sqrt 6 : ℝ) = (3 / Real.sqrt 6 : ℝ) := by ring
      rw [h3]
      have h4 : (3 / Real.sqrt 6 : ℝ) = Real.sqrt 6 / 2 := by
        have h5 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := h1
        field_simp [h5]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num : (6 : ℝ) > 0)]
      linarith [h4]
  · -- Show that sqrt(3/2) is greatest in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h3 : (a + b + c) ^ 2 ≤ 3 / 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h3' : a + b + c ≥ 0 := by linarith
    have h4' : Real.sqrt (3 / 2) ≥ 0 := by positivity
    have h6 : a + b + c ≤ Real.sqrt (3 / 2) := by
      have h7 : (a + b + c) ^ 2 ≤ (3 / 2) := h3
      have h8 : (Real.sqrt (3 / 2)) ^ 2 = (3 / 2) := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg (3 / 2), show 0 ≤ (a + b + c : ℝ) by linarith, Real.sqrt_nonneg (3 / 2)]
    linarith [h6, hx]