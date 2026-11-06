import Mathlib

theorem algebra_176366 (a b c d : ℝ) (h : ∀ x : ℝ, |x| ≤ 1 → |a * x ^ 3 + b * x ^ 2 + c * x + d| ≤ 1) :
    ∀ x : ℝ, |x| < 1 → |3 * a * x ^ 2 + 2 * b * x + c| ≤ 9 := by
  intro x hx
  have h1 := h 1 (by
    norm_num
  )
  have h2 := h (-1) (by
    norm_num
  )
  have h3 := h (1 / 2) (by
    norm_num [abs_le]
  )
  have h4 := h (-1 / 2) (by
    norm_num [abs_le]
  )
  have h5 := h (0) (by
    norm_num [abs_le]
  )
  cases' abs_lt.mp hx with hx1 hx2
  have h11 : -1 ≤ a + b + c + d := by
    norm_num [abs_le] at h1
    linarith
  have h12 : a + b + c + d ≤ 1 := by
    norm_num [abs_le] at h1
    linarith
  have h21 : -1 ≤ -a + b - c + d := by
    norm_num [abs_le] at h2
    linarith
  have h22 : -a + b - c + d ≤ 1 := by
    norm_num [abs_le] at h2
    linarith
  have h31 : -1 ≤ a / 8 + b / 4 + c / 2 + d := by
    norm_num [abs_le] at h3
    linarith
  have h32 : a / 8 + b / 4 + c / 2 + d ≤ 1 := by
    norm_num [abs_le] at h3
    linarith
  have h41 : -1 ≤ -a / 8 + b / 4 - c / 2 + d := by
    norm_num [abs_le] at h4
    linarith
  have h42 : -a / 8 + b / 4 - c / 2 + d ≤ 1 := by
    norm_num [abs_le] at h4
    linarith
  have h51 : -1 ≤ d := by
    norm_num [abs_le] at h5
    linarith
  have h52 : d ≤ 1 := by
    norm_num [abs_le] at h5
    linarith
  apply abs_le.mpr
  constructor
  · -- Prove -9 ≤ 3 * a * x^2 + 2 * b * x + c
    nlinarith [sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x), mul_pos (sub_pos.mpr (show -1 < x by linarith)) (sub_pos.mpr (show x < 1 by linarith))]
  · -- Prove 3 * a * x^2 + 2 * b * x + c ≤ 9
    nlinarith [sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x), mul_pos (sub_pos.mpr (show -1 < x by linarith)) (sub_pos.mpr (show x < 1 by linarith))]