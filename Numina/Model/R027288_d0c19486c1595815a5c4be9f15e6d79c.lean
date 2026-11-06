import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_320638 :
  IsGreatest {x | ∃ a b c : ℝ, a^2 + b^2 ≤ c ∧ c ≤ 1 ∧ x = a + b + c} (1 + sqrt 2) ∧
  IsLeast {x | ∃ a b c : ℝ, a^2 + b^2 ≤ c ∧ c ≤ 1 ∧ x = a + b + c} (-1 / 2) := by 
  constructor 
  · -- First part: proving 1 + Real.sqrt 2 is greatest 
    constructor
    · -- Show that 1 + Real.sqrt 2 belongs to the set 
      use Real.sqrt (1 / 2), Real.sqrt (1 / 2), 1
      have h1 : (Real.sqrt (1 / 2 : ℝ) : ℝ) ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
      constructor
      · -- Show a^2 + b^2 ≤ c 
        nlinarith [h1, Real.sqrt_nonneg (1 / 2 : ℝ), Real.sqrt_nonneg (1 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
      constructor 
      · -- Show c ≤ 1 
        norm_num 
      · -- Show 1 + sqrt 2 = a + b + c 
        have h2 : (Real.sqrt (1 / 2 : ℝ) : ℝ) = Real.sqrt 2 / 2 := by
          have h2 : (Real.sqrt (1 / 2 : ℝ) : ℝ) = Real.sqrt 2 / 2 := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf
            <;> norm_num 
            all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          linarith
        nlinarith [h2, Real.sqrt_nonneg (1 / 2 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (1 / 2 : ℝ)]
    · -- Show that 1 + Real.sqrt 2 is greatest 
      intro x hx 
      rcases hx with ⟨a, b, c, h1, h2, h3⟩
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - Real.sqrt 2), sq_nonneg (a - (Real.sqrt 2 / 2)), sq_nonneg (b - (Real.sqrt 2 / 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (c - 1)]
  · -- Second part: proving -1/2 is the least 
    constructor
    · -- Show that -1/2 belongs to the set 
      use (-1 / 2 : ℝ), (-1 / 2 : ℝ), (1 / 2 : ℝ)
      constructor
      · -- Show a^2 + b^2 ≤ c 
        norm_num
      constructor 
      · -- Show c ≤ 1 
        norm_num 
      · -- Show -1/2 = a + b + c 
        norm_num 
    · -- Show that -1/2 is the least 
      intro x hx 
      rcases hx with ⟨a, b, c, h1, h2, h3⟩
      nlinarith [sq_nonneg (a + 1 / 2), sq_nonneg (b + 1 / 2), sq_nonneg (c - (a^2 + b^2)), sq_nonneg (c - 1 / 2)]