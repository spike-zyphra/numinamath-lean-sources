import Mathlib

theorem algebra_204327 {x : ℝ} (hx : x = (4 ^ ((1 : ℝ) / 3) + 2 ^ ((1 : ℝ) / 3) + 1)) :
    (1 + 1 / x) ^ 3 = 2 := by
  have h1 : (4 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  have h3 : (4 : ℝ) ^ ((1 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    rw [h1]
    have h4 : (2 : ℝ) ^ ((2 : ℝ) / 3) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals linarith
    linarith [h4]
  have h4 : x = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
    rw [hx]
    rw [h3]
    all_goals ring_nf
  have h5 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h7 : (2 : ℝ) ^ ((1 : ℝ) / 3) ≠ (1 : ℝ) := by
    by_contra h
    have h8 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (1 : ℝ) := by
      rw [h]
      norm_num
    have h9 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := h5
    linarith
  have h9 : x = 1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) := by
    have h9' : (x) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + (2 : ℝ) ^ ((1 : ℝ) / 3) + 1 := h4
    have h11' : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (2 : ℝ) := h5
    have h9 : ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) ≠ 0 := by
      by_contra h'
      have h11 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) = (1 : ℝ) := by linarith
      have h12 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (1 : ℝ) := by
        rw [h11]
        norm_num
      nlinarith [h5]
    -- Now, need to prove that (a - 1) * x = 1
    have h16 : ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) * (x) = (1 : ℝ) := by
      rw [h9']
      have h17 : ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) * (((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + (2 : ℝ) ^ ((1 : ℝ) / 3) + 1) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - 1 := by
        ring_nf
      rw [h17]
      nlinarith [h11']
    field_simp [(show ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) ≠ 0 by
      exact h9
    )] at h16 ⊢
    <;> nlinarith
  have h10 : (1 / x) = (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 := by
    rw [h9]
    field_simp [(show ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) ≠ 0 by
      intro h'
      have h12 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) = (1 : ℝ) := by linarith
      have h13 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (1 : ℝ) := by
        rw [h12]
        norm_num
      nlinarith [h5]
    )
    ]
  have h6 : (1 + 1 / x) = ((2 : ℝ) ^ ((1 : ℝ) / 3)) := by
    rw [h10]
    ring
  rw [h6]
  exact h5