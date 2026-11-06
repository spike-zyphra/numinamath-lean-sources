import Mathlib

theorem algebra_14571 (k : ℝ) (hk : k ≠ 0) : (1 / (2 * k)) ^ (-2 : ℝ) * (-k) ^ 3 = -4 * k ^ 5 := by
  have h1 : (1 / (2 * k)) ^ (-2 : ℝ) = (2 * k) ^ 2 := by
    have h4 : (1 / (2 * k)) ^ (-2 : ℝ) = ((2 * k) ^ (2 : ℝ)) := by
      have h5 : (1 / (2 * k)) ^ (-2 : ℝ) = ( (1 / (2 * k)) ^ (-2 : ℤ) ) := by
        norm_cast
      rw [h5]
      simp [zpow_neg, zpow_ofNat]
      <;> field_simp <;> ring
    rw [h4]
    all_goals norm_cast
  rw [h1]
  ring_nf
  <;> nlinarith [sq_nonneg k, sq_nonneg (k + 1), sq_nonneg (k - 1)]