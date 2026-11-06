import Mathlib

theorem algebra_151134 (a b : ℝ × ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : (a.1 + 3 * b.1) * (7 * a.1 - 5 * b.1) + (a.2 + 3 * b.2) * (7 * a.2 - 5 * b.2) = 0)
    (h2 : (a.1 - 4 * b.1) * (7 * a.1 - 2 * b.1) + (a.2 - 4 * b.2) * (7 * a.2 - 2 * b.2) = 0) :
    Real.pi / 3 = Real.arccos ((a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2))) := by
  have eq1 : 7 * (a.1 ^ 2 + a.2 ^ 2) + 16 * (a.1 * b.1 + a.2 * b.2) - 15 * (b.1 ^ 2 + b.2 ^ 2) = 0 := by
    nlinarith
  have eq2 : 7 * (a.1 ^ 2 + a.2 ^ 2) - 30 * (a.1 * b.1 + a.2 * b.2) + 8 * (b.1 ^ 2 + b.2 ^ 2) = 0 := by
    nlinarith
  have eq3 : 2 * (a.1 * b.1 + a.2 * b.2) = b.1 ^ 2 + b.2 ^ 2 := by
    nlinarith
  have eq4 : a.1 ^ 2 + a.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := by 
    nlinarith
  have h5 : a.1 ^ 2 + a.2 ^ 2 > 0 := by
    have h6 : a.1 ^ 2 + a.2 ^ 2 > 0 := by
      by_contra h7
      push_neg at h7
      have h8 : a.1 ^ 2 = 0 := by nlinarith [h7, sq_nonneg (a.1), sq_nonneg (a.2)]
      have h9 : a.1 = 0 := by
        nlinarith
      have h10 : a.2 ^ 2 = 0 := by nlinarith [h7, sq_nonneg (a.1), sq_nonneg (a.2)]
      have h11 : a.2 = 0 := by
        nlinarith
      have h14 : a = (0, 0) := by 
        simp [Prod.ext_iff, h9, h11]
      contradiction
    linarith
  have h7 : b.1 ^ 2 + b.2 ^ 2 > 0 := by
    have h8 : b.1 ^ 2 + b.2 ^ 2 > 0 := by
      by_contra h9
      push_neg at h9
      have h10 : b.1 ^ 2 = 0 := by nlinarith [h9, sq_nonneg (b.1), sq_nonneg (b.2)]
      have h11 : b.1 = 0 := by
        nlinarith
      have h12 : b.2 ^ 2 = 0 := by nlinarith [h9, sq_nonneg (b.1), sq_nonneg (b.2)]
      have h13 : b.2 = 0 := by
        nlinarith
      have h16 : b = (0, 0) := by 
        simp [Prod.ext_iff, h11, h13]
      contradiction
    linarith
  have h3 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2) = 2 * (a.1 * b.1 + a.2 * b.2) := by 
    have h8 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2) = Real.sqrt ((a.1 ^ 2 + a.2 ^ 2) * (b.1 ^ 2 + b.2 ^ 2)) := by
      rw [← Real.sqrt_mul (by positivity)]
    have h5a : a.1 ^ 2 + a.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := eq4
    have h5b : b.1 ^ 2 + b.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := by linarith [eq3]
    have h9 : (a.1 ^ 2 + a.2 ^ 2) * (b.1 ^ 2 + b.2 ^ 2) = (2 * (a.1 * b.1 + a.2 * b.2)) ^ 2 := by
      rw [show a.1 ^ 2 + a.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) by linarith]
      rw [show b.1 ^ 2 + b.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) by linarith]
      <;> nlinarith
    rw [h9] at h8
    have h10 : Real.sqrt ((2 * (a.1 * b.1 + a.2 * b.2)) ^ 2) = abs (2 * (a.1 * b.1 + a.2 * b.2)) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h10] at h8 
    have h11 : 2 * (a.1 * b.1 + a.2 * b.2) ≥ 0 := by
      by_contra h12
      push_neg at h12
      have h12a : b.1 ^ 2 + b.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := by linarith [eq3]
      nlinarith [sq_nonneg (a.1 * b.1 + a.2 * b.2), sq_nonneg (a.1 - b.1), sq_nonneg (a.2 - b.2), sq_nonneg (a.1 + b.1), sq_nonneg (a.2 + b.2), sq_pos_of_pos h5, sq_pos_of_pos h7, Real.sqrt_nonneg (a.1 ^ 2 + a.2 ^ 2), Real.sqrt_nonneg (b.1 ^ 2 + b.2 ^ 2)]
    rw [abs_of_nonneg h11] at h8
    linarith
  have hcos : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2)) = 1 / 2 := by
    have hb' : a.1 * b.1 + a.2 * b.2 ≠ 0 := by
      by_contra hzero
      rw [hzero] at eq4 eq3
      have hzero2 : a.1 ^ 2 + a.2 ^ 2 = 0 := by linarith
      have hzero3 : a.1 = 0 := by nlinarith [sq_nonneg (a.1), sq_nonneg (a.2), hzero2]
      have hzero4 : a.2 = 0 := by nlinarith [sq_nonneg (a.1), sq_nonneg (a.2), hzero2]
      have hzero1 : a = (0, 0) := by 
        simp [Prod.ext_iff, hzero3, hzero4]
      contradiction
    rw [h3]
    field_simp [hb']
    <;> nlinarith
  rw [hcos]
  have h4 : Real.arccos (1 / 2) = Real.pi / 3 := by 
    have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [← h4]
    apply Real.arccos_cos
    all_goals linarith [Real.pi_pos]
  linarith [h4]