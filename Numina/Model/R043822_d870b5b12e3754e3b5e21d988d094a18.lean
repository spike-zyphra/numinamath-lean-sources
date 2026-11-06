import Mathlib

theorem algebra_220559 : ∃ n : ℕ, ((7 + 5 * √2) ^ ((1 : ℝ) / 3) * (Real.sqrt 2 - 1)) / (√(4 + 2 * √3) - √3) = n := by
  use 1
  have h1 : (7 + 5 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = Real.sqrt 2 + 1 := by
    have h2 : (Real.sqrt 2 + 1) ^ 3 = (7 + 5 * Real.sqrt 2 : ℝ) := by
      have h3 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      calc
        (Real.sqrt 2 + 1 : ℝ) ^ 3 = (Real.sqrt 2) ^ 3 + (3 * (Real.sqrt 2) ^ 2 * 1) + (3 * Real.sqrt 2 * (1 : ℝ) ^ 2) + (1 : ℝ) ^ 3 := by ring
        _ = (Real.sqrt 2) * (Real.sqrt 2) ^ 2 + 3 * (Real.sqrt 2) ^ 2 + 3 * Real.sqrt 2 + 1 := by ring_nf
        _ = (Real.sqrt 2) * (2 : ℝ) + 3 * (2 : ℝ) + 3 * Real.sqrt 2 + 1 := by rw [h3]
        _ = 2 * Real.sqrt 2 + (6 : ℝ) + 3 * Real.sqrt 2 + 1 := by ring_nf
        _ = 7 + 5 * Real.sqrt 2 := by ring_nf
    have h3 : (7 + 5 * Real.sqrt 2) = (Real.sqrt 2 + 1) ^ 3 := by
      nlinarith [h2]
    rw [h3]
    have h4 : 0 ≤ Real.sqrt 2 + 1 := by
      have h11 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > (0 : ℝ)), h11]
    have h5 : ((Real.sqrt 2 + 1) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (Real.sqrt 2 + 1 : ℝ) := by
      have h6 : ((Real.sqrt 2 + 1) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (Real.sqrt 2 + 1 : ℝ) := by
        have h8 : ((Real.sqrt 2 + 1 : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (Real.sqrt 2 + 1 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        norm_cast at h8 ⊢
        all_goals nlinarith [h8]
      exact h6
    exact h5
  have h2 : ((7 + 5 * Real.sqrt 2) ^ ((1 : ℝ) / 3) * (Real.sqrt 2 - 1)) = 1 := by
    rw [h1]
    have h22 : (Real.sqrt 2 + 1 : ℝ) * (Real.sqrt 2 - 1 : ℝ) = 1 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
    nlinarith
  have h3 : Real.sqrt (4 + 2 * Real.sqrt 3) = Real.sqrt 3 + 1 := by
    have h4 : Real.sqrt (4 + 2 * Real.sqrt 3) = (Real.sqrt 3 + 1 : ℝ) := by
      have h5 : (Real.sqrt 3 + 1 : ℝ) ^ 2 = (4 + 2 * Real.sqrt 3 : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0: ℝ) ≤ (3: ℝ) by norm_num)]
      have h6 : (0 : ℝ) ≤ (Real.sqrt 3 + 1 : ℝ) := by
        have h7 : 0 ≤ Real.sqrt 3 := by apply Real.sqrt_nonneg
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      rw [←h5]
      field_simp [Real.sqrt_nonneg (4 + 2 * Real.sqrt 3), Real.sqrt_nonneg (3 : ℝ)]
      all_goals nlinarith [Real.sqrt_nonneg (4 + 2 * Real.sqrt 3), Real.sqrt_nonneg (3 : ℝ)]
    exact h4
  have h4 : Real.sqrt (4 + 2 * Real.sqrt 3) - Real.sqrt 3 = 1 := by
    rw [h3]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (4 + 2 * (3 : ℝ))]
  rw [h2, h4]
  all_goals norm_num