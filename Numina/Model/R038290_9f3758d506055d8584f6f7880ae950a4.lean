import Mathlib

theorem algebra_308353 {a x : ℝ} {n : ℕ} (ha : a ≠ 0) (h : a ^ n = x) (h' : a ^ (-n : ℤ) = Real.sqrt 2 + 1) :
    a ^ (3 * n) + a ^ (-3 * n : ℤ) = 10 * Real.sqrt 2 := by
  have ha1 : a ^ (-n : ℤ) = 1 / (a ^ n) := by
    simp [zpow_neg, zpow_ofNat]

  have eq1 : a ^ n = Real.sqrt 2 - 1 := by
    have eq2 : a ^ (-n : ℤ) = (1 / (a ^ n : ℝ)) := by
      simp [zpow_neg, zpow_ofNat]

    rw [eq2] at h'
    have hx1 : (a ^ n : ℝ) ≠ 0 := by
      by_contra h1
      have h2 : (1 / (a ^ n : ℝ) ) = 0 := by
        rw [h1]
        norm_num
      rw [h'] at h2
      nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num), Real.sqrt_nonneg (2:ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

    field_simp [hx1] at h' ⊢
    nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num), Real.sqrt_nonneg (2:ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have eq2 : a ^ (3 * n) = (a ^ n) ^ 3 := by
    rw [← pow_mul]
    ring_nf

  have eq3 : a ^ (-3 * n : ℤ) = (a ^ (-n : ℤ)) ^ 3 := by
    rw [← zpow_natCast, ← zpow_mul]
    ring_nf
    all_goals omega

  have eq4 : (a ^ n) ^ 3 = (Real.sqrt 2 - 1) ^ 3 := by
    rw [eq1]

  have eq5 : (a ^ (-n : ℤ)) ^ 3 = (Real.sqrt 2 + 1) ^ 3 := by
    rw [h']

  rw [eq2, eq4, eq3, eq5]
  nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (2:ℝ) by norm_num), Real.sqrt_nonneg (2:ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]