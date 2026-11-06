import Mathlib

theorem algebra_187320 {u v : ℝ} (hu : u ≥ 0) (hv : v ≥ 0)
    (h1 : (u : ℝ) ^ ((1 : ℝ) / 4) - (v : ℝ) ^ ((1 : ℝ) / 4) = 1)
    (h2 : Real.sqrt u + Real.sqrt v = 5) :
    u = 16 ∧ v = 1 := by

  have h3 : Real.sqrt u = ((u : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
    have h4 : ((u : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (u : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h5 : Real.sqrt u = (u : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h5]
    linarith [h4]
  have h6 : Real.sqrt v = ((v : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
    have h7 : ((v : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (v : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h8 : Real.sqrt v = (v : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h8]
    linarith [h7]
  have eq1 : ((u : ℝ) ^ ((1 : ℝ) / 4)) = (v : ℝ) ^ ((1 : ℝ) / 4) + 1 := by linarith
  have eq2 : ((u : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 + ((v : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 = 5 := by
    have h7 : Real.sqrt u + Real.sqrt v = 5 := h2
    rw [h3, h6] at h7
    nlinarith
  have eq4 : ((v : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 + ((v : ℝ) ^ ((1 : ℝ) / 4) ) - 2 = 0 := by
    have eq1' : ((u : ℝ) ^ ((1 : ℝ) / 4)) = (v : ℝ) ^ ((1 : ℝ) / 4) + 1 := eq1
    rw [eq1'] at eq2
    nlinarith
  have eq5 : (v : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
    have h9 : ((v : ℝ) ^ ((1 : ℝ) / 4) ) ^ 2 + ((v : ℝ) ^ ((1 : ℝ) / 4) ) - 2 = 0 := eq4
    have h10 : ((v : ℝ) ^ ((1 : ℝ) / 4) - 1) * ((v : ℝ) ^ ((1 : ℝ) / 4) + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- case $b - 1 =0$
      linarith
    · -- case $b + 2 =0$ 
      have h13 : (v : ℝ) ^ ((1 : ℝ) / 4) = -2 := by linarith
      have h14 : (v : ℝ) ^ ((1 : ℝ) / 4) ≥ 0 := by positivity
      nlinarith
  have eq6 : (u : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
    have eq1' : (u : ℝ) ^ ((1 : ℝ) / 4) = (v : ℝ) ^ ((1 : ℝ) / 4) + 1 := eq1
    have eq5' : (v : ℝ) ^ ((1 : ℝ) / 4) = 1 := eq5
    linarith
  have h7 : u = 16 := by
    have h8 : (u : ℝ) ^ ((1 : ℝ) / 4) = 2 := eq6
    have h9 : ((u : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (2 : ℝ) ^ 4 := by
      rw [h8]
    have h10 : ((u : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (u : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h11 : (2 : ℝ) ^ 4 = (16 : ℝ) := by norm_num
    nlinarith [h10, h11, h9]
  have h8 : v = 1 := by
    have h9 : (v : ℝ) ^ ((1 : ℝ) / 4) = 1 := eq5
    have h10 : ((v : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (1 : ℝ) ^ 4 := by
      rw [h9]
    have h11 : ((v : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (v : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h12 : (1 : ℝ) ^ 4 = (1 : ℝ) := by norm_num
    nlinarith [h11, h12, h10]
  exact ⟨h7, h8⟩