import Mathlib

theorem algebra_160429 (x : ℝ) (h : (2 : ℝ)^x = 3) : (4 : ℝ)^(3 * x + 2) = 11664 := by
  have h1 : (4 : ℝ) ^ (3 * x + 2) = (2 : ℝ) ^ (6 * x + 4) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
    have h2 : ((2 : ℝ) ^ (2 : ℝ) : ℝ) ^ (3 * x + 2) = (2 : ℝ) ^ (2 * (3 * x + 2) : ℝ) := by
      rw [← Real.rpow_mul]
      all_goals ring_nf
      all_goals linarith
    -- expanding $(2 ^ 2) ^ {3 * x + 2}$ as $2 ^ {6 * x + 4}$
    rw [h2]
    ring_nf
    <;> norm_num
    <;> ring_nf <;> norm_num
    <;> linarith
  rw [h1]
  have h4 : (2 : ℝ) ^ (6 * x + 4) = ((2 : ℝ) ^ x) ^ (6 : ℝ) * ((2 : ℝ) ^ (4 : ℝ)) := by
    have h5 : (2 : ℝ) ^ (6 * x + 4) = (2 : ℝ) ^ (6 * x) * (2 : ℝ) ^ (4 : ℝ) := by
      rw [← Real.rpow_add]
      all_goals ring_nf
      all_goals linarith
    have h6 : (2 : ℝ) ^ (6 * x) = ((2 : ℝ) ^ x) ^ (6 : ℝ) := by
      have h7 : ((2 : ℝ) ^ x) ^ (6 : ℝ) = (2 : ℝ) ^ (x * (6 : ℝ)) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
        all_goals try norm_num
      have h8 : (x * (6 : ℝ)) = (6 * x : ℝ) := by
        ring_nf
      rw [show (6 * x : ℝ) = (x * (6 : ℝ) : ℝ) by ring] at *
      rw [h7]
      <;> ring_nf <;> norm_num
      all_goals linarith
    rw [h5, h6]
  rw [h4]
  rw [h]
  norm_num