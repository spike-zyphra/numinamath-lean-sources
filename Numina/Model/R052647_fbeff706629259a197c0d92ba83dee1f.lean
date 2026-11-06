import Mathlib

theorem number_theory_293542 (n : ℕ) (hn : n > 0) :
    ∃ a : ℝ, a > 0 ∧ a ≠ 1 ∧ (1 / a) ^ n = 1 + Real.sqrt 2 := by
  use (1 / ((1 + Real.sqrt 2) ^ (1 / n : ℝ)))
  constructor
  · -- Prove that a > 0
    positivity
  constructor
  · -- Prove that a ≠ 1
    by_contra h
    have h1 : (1 / ((1 + Real.sqrt 2) ^ (1 / n : ℝ))) = 1 := by
      linarith
    have h2 : (1 + Real.sqrt 2) ^ (1 / n : ℝ) = 1 := by
      field_simp at h1 ⊢
      linarith
    have h3 : (1 + Real.sqrt 2) ^ (1 / n : ℝ) > 1 := by
      have h4 : (1 + Real.sqrt 2) > (1 : ℝ) := by
        have h5 : Real.sqrt (2 : ℝ) > (1 : ℝ) := by
          have h6 : Real.sqrt (2 : ℝ) > Real.sqrt (1 : ℝ) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          have h7 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
          linarith
        linarith
      have h5 : (1 / n : ℝ) > 0 := by 
        have hn' : (n : ℝ) > 0 := by exact_mod_cast hn
        positivity
      have h6 : (1 + Real.sqrt 2) ^ (1 / n : ℝ) > (1 : ℝ) ^ (1 / n : ℝ) := by
        apply Real.rpow_lt_rpow
        · linarith
        · linarith
        all_goals linarith [h5]
      have h7 : (1 : ℝ) ^ (1 / n : ℝ) = 1 := by 
        simp [Real.one_rpow]
      linarith [h6, h7]
    linarith [h2, h3]
  · -- Prove that (1 / a)^n = 1 + Real.sqrt 2
    have h3 : ((1 + Real.sqrt 2) ^ (1 / n : ℝ)) ^ (n : ℕ) = (1 + Real.sqrt 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      field_simp
      all_goals norm_num
      all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    field_simp [h3]
    <;> norm_num
    <;> linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]