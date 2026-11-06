import Mathlib

theorem algebra_182922 (x y z : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z)
    (h₁ : x ^ Real.logb y z = 2) (h₂ : y ^ Real.logb z x = 4) (h₃ : z ^ Real.logb x y = 8) :
    Real.logb x y = Real.sqrt 3 := by
  have h4 : Real.logb y z * Real.log x = Real.log 2 := by
    have h5 : Real.log (x ^ Real.logb y z) = Real.log 2 := by
      rw [h₁]
      all_goals linarith
    have h6 : Real.log (x ^ Real.logb y z) = Real.logb y z * Real.log x := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h5, h6]
  have h7 : Real.logb z x * Real.log y = Real.log 4 := by
    have h8 : Real.log (y ^ Real.logb z x) = Real.log 4 := by
      rw [h₂]
      all_goals linarith
    have h9 : Real.log (y ^ Real.logb z x) = Real.logb z x * Real.log y := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h8, h9]
  have h10 : Real.logb x y * Real.log z = Real.log 8 := by
    have h11 : Real.log (z ^ Real.logb x y) = Real.log 8 := by
      rw [h₃]
      all_goals linarith
    have h12 : Real.log (z ^ Real.logb x y) = Real.logb x y * Real.log z := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h11, h12]
  have h_eq1 : Real.logb y z = Real.log z / Real.log y := by
    field_simp [Real.logb]
  have h_eq2 : Real.logb z x = Real.log x / Real.log z := by
    field_simp [Real.logb]
  have h_eq3 : Real.logb x y = Real.log y / Real.log x := by
    field_simp [Real.logb]
  have h11 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log (2 ^ 2 : ℝ) := by norm_num
      _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
  have h12 : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log (2 ^ 3 : ℝ) := by norm_num
      _ = 3 * Real.log (2 : ℝ) := by simp [Real.log_pow]
  rw [h_eq1] at h4
  rw [h_eq2] at h7
  rw [h_eq3] at h10
  rw [h11] at h7
  rw [h12] at h10
  have hx_pos : 0 < Real.log x := by
    apply Real.log_pos
    linarith
  have hy_pos : 0 < Real.log y := by
    apply Real.log_pos
    linarith
  have hz_pos : 0 < Real.log z := by
    apply Real.log_pos
    linarith
  have h_eq4 : (Real.log y) ^ 2 = 3 * (Real.log x) ^ 2 := by
    field_simp [show Real.log y ≠ 0 by linarith, show Real.log z ≠ 0 by linarith] at h4 h7 h10
    nlinarith [sq_nonneg (Real.log x - Real.log y), sq_nonneg (Real.log y - Real.log z), sq_nonneg (Real.log z - Real.log x)]
  have h_eq5 : (Real.log y / Real.log x) ^ 2 = 3 := by
    have hx_pos' : 0 < Real.log x := hx_pos
    field_simp at *
    nlinarith
  have h_eq6 : Real.logb x y = Real.sqrt 3 := by
    rw [h_eq3]
    have h11 : (Real.log y / Real.log x) ^ 2 = 3 := h_eq5
    have h_eq7 : Real.log y / Real.log x = Real.sqrt 3 := by
      have h14 : (Real.log y / Real.log x) ^ 2 = 3 := h_eq5
      have h15 : 0 ≤ Real.sqrt 3 := by positivity
      have h_eq8 : Real.log y / Real.log x ≥ 0 := by
        have h16 : Real.log y / Real.log x > 0 := by
          apply div_pos
          all_goals linarith
        linarith
      have h_eq9 : Real.log y / Real.log x = Real.sqrt 3 := by
        have h_eq10 : (Real.log y / Real.log x) ^ 2 - 3 = 0 := by linarith
        have h_eq11 : (Real.log y / Real.log x - Real.sqrt 3) * (Real.log y / Real.log x + Real.sqrt 3) = 0 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        cases' (mul_eq_zero.mp h_eq11) with h_eq12 h_eq13
        · -- $\log_{x} y - \sqrt{3} = 0$
          linarith
        · -- $\log_{x} y + \sqrt{3} = 0$
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
      linarith
    field_simp at h_eq7 ⊢
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  linarith [h_eq6]