import Mathlib


theorem algebra_166514 {u v : ℝ} (hu : u > 0) (hv : v > 0)
    (h1 : u^(-1 / 2 : ℝ) * u^(1 / 3 : ℝ) + v^(-1 / 2 : ℝ) * v^(1 / 3 : ℝ) = 1.5)
    (h2 : u * v = 64) :
    (u = 1 ∧ v = 64) ∨ (u = 64 ∧ v = 1) := by
  have eq1 : u ^ (-1 / 2 : ℝ) * u ^ (1 / 3 : ℝ) = u ^ (-1 / 6 : ℝ) := by
    rw [← Real.rpow_add]
    norm_num
    all_goals linarith
  have eq2 : v ^ (-1 / 2 : ℝ) * v ^ (1 / 3 : ℝ) = v ^ (-1 / 6 : ℝ) := by
    rw [← Real.rpow_add]
    norm_num
    all_goals linarith
  have eq3 : u ^ (-1 / 6 : ℝ) + v ^ (-1 / 6 : ℝ) = 1.5 := by
    rw [eq1, eq2] at h1
    nlinarith
  have eq4 : u ^ (-1 / 6 : ℝ) * v ^ (-1 / 6 : ℝ) = 0.5 := by
    have h3 : u ^ (-1 / 6 : ℝ) * v ^ (-1 / 6 : ℝ) = (u * v) ^ (-1 / 6 : ℝ) := by
      rw [← Real.mul_rpow]
      all_goals nlinarith
    rw [h3, h2]
    have h5 : (64 : ℝ) ^ (-1 / 6 : ℝ) = 0.5 := by
      have h6 : (64 : ℝ) ^ (-1 / 6 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
        have h7 : (64 : ℝ) = (2 : ℝ) ^ (6 : ℝ) := by norm_num
        rw [h7]
        have h8 : ((2: ℝ) ^ (6: ℝ)) ^ (-1 / 6 : ℝ) = (2 : ℝ) ^ (6 * (-1 / 6): ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals linarith
        norm_num at h8 ⊢
        all_goals linarith
      rw [h6]
      norm_num
    linarith [h5]
  have eq5 : (u ^ (-1 / 6 : ℝ) - 1) * (u ^ (-1 / 6 : ℝ) - 0.5) = 0 := by
    nlinarith [sq_nonneg (u ^ (-1 / 6 : ℝ) - v ^ (-1 / 6 : ℝ)), sq_nonneg (u ^ (-1 / 6 : ℝ) - 1), sq_nonneg (v ^ (-1 / 6 : ℝ) - 1), sq_nonneg (u ^ (-1 / 6 : ℝ) - 0.5), sq_nonneg (v ^ (-1 / 6 : ℝ) - 0.5)]
  cases' (mul_eq_zero.1 eq5) with h7 h8
  · -- case $u = 1$.
    have h8 : u ^ (-1 / 6 : ℝ) = 1 := by linarith
    have h9 : u = 1 := by
      have h10 : u ^ (-1 / 6 : ℝ) = 1 := h8
      have h11 : u = (u ^ (-1 / 6 : ℝ)) ^ (-6 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith
      rw [h10] at h11
      have h12 : (1 : ℝ) ^ (-6 : ℝ) = 1 := by
        norm_num
      linarith [h11, h12]
    have h10 : v = 64 := by
      nlinarith
    left
    exact ⟨h9, h10⟩
  · -- case $u = 64$.
    have h8 : u ^ (-1 / 6 : ℝ) = 0.5 := by
      nlinarith
    have h9 : u = 64 := by
      have h11 : u = (u ^ (-1 / 6 : ℝ)) ^ (-6 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith
      rw [h8] at h11
      have h13 : (0.5 : ℝ) ^ (-6 : ℝ) = 64 := by
        norm_num
      nlinarith [h11, h13]
    have h10 : v = 1 := by
      nlinarith
    right
    exact ⟨h9, h10⟩