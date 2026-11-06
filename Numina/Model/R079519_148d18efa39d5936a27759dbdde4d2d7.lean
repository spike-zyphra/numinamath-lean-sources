import Mathlib

theorem algebra_11954 : IsLeast {x : ℝ | x ≠ 2 ∧ x ≠ 4 ∧ x ≠ 3 ∧ 1 / (x - 2) + 1 / (x - 4) = 3 / (x - 3)} (3 - Real.sqrt 3) := by
  constructor
  · -- Show that 3 - sqrt(3) is in the set
    constructor
    · -- Show that 3 - sqrt(3) ≠ 2
      have h1 : (3 - Real.sqrt 3) ≠ 2 := by
        by_contra h
        have h2 : Real.sqrt 3 = 1 := by linarith
        have h3 : Real.sqrt 3 ^ 2 = (1 : ℝ) := by
          rw [h2]
          all_goals nlinarith
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      exact h1
    constructor
    · -- Show that 3 - sqrt(3) ≠ 4
      have h1 : (3 - Real.sqrt 3) ≠ 4 := by
        by_contra h
        have h2 : Real.sqrt 3 = -1 := by linarith
        have h3 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg (3 : ℝ)
        nlinarith [Real.sqrt_nonneg (3 : ℝ)]
      exact h1
    constructor
    · -- Show that 3 - sqrt(3) ≠ 3
      have h1 : (3 - Real.sqrt 3) ≠ 3 := by
        by_contra h
        have h2 : Real.sqrt 3 = 0 := by linarith
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      exact h1
    · -- Verify that 3 - sqrt(3) is a solution
      have h_eq : 1 / ((3 - Real.sqrt 3) - 2) + 1 / ((3 - Real.sqrt 3) - 4) = 3 / ((3 - Real.sqrt 3) - 3) := by
        have h1 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        have h2 : (3 - Real.sqrt 3 - 2) ≠ 0 := by
          intro h
          have h_zero : Real.sqrt 3 = 1 := by linarith
          have h_zero_2 : Real.sqrt 3 ^ 2 = (1 : ℝ) := by
            rw [h_zero]
            all_goals nlinarith
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        have h3 : (3 - Real.sqrt 3 - 4) ≠ 0 := by
          intro h
          have h_zero : Real.sqrt 3 = -1 := by linarith
          have h3_pos : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg (3 : ℝ)
          nlinarith [Real.sqrt_nonneg (3 : ℝ)]
        have h4 : (3 - Real.sqrt 3 - 3) ≠ 0 := by
          intro h
          have h_zero : Real.sqrt 3 = 0 := by linarith
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        field_simp [(show (3 - Real.sqrt 3 - 2) ≠ 0 by exact h2),
         (show (3 - Real.sqrt 3 - 4) ≠ 0 by exact h3),
         (show (3 - Real.sqrt 3 - 3) ≠ 0 by exact h4)]
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt (3 : ℝ)), sq_nonneg (2 - Real.sqrt 3)]
      exact h_eq
  · -- Show that 3 - sqrt(3) is the smallest
    intro y hy
    rcases hy with ⟨hy2, hy4, hy3, heq⟩
    have h_eq : 1 / (y - 2) + 1 / (y - 4) = 3 / (y - 3) := heq
    have h1 : (y - 2) ≠ 0 := by
      intro h
      apply hy2
      linarith
    have h2 : (y - 4) ≠ 0 := by
      intro h
      apply hy4
      linarith
    have h3 : (y - 3) ≠ 0 := by
      intro h
      apply hy3
      linarith
    field_simp [(show y - 2 ≠ 0 by exact h1), (show y - 4 ≠ 0 by exact h2), (show y - 3 ≠ 0 by exact h3)] at h_eq
    ring_nf at h_eq
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (y - (3 : ℝ)), sq_nonneg (y - (3 - Real.sqrt 3)), sq_nonneg (y - (3 + Real.sqrt 3))]