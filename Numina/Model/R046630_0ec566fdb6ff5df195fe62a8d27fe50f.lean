import Mathlib

theorem algebra_102451 (θ : ℝ) (hθ : 0 < θ ∧ θ < Real.pi / 4)
    (h : 1 / Real.sin θ - 1 / Real.cos θ = Real.sqrt 13 / 6) :
    1 / Real.tan θ - Real.tan θ = 5 / 6 := by

  have h1 : 0 < θ := hθ.1
  have h2 : θ < Real.pi / 4 := hθ.2
  have h3 : Real.sin θ > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h4 : Real.cos θ > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos, h1, h2]
    linarith [Real.pi_pos, h1, h2]
  have h5 : Real.sin θ < Real.cos θ := by
    have h6 : θ < Real.pi / 4 := h2
    have h7 : Real.sin θ < Real.sin (Real.pi / 2 - θ) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos, h1, h2]
    have h9 : Real.sin (Real.pi / 2 - θ) = Real.cos θ := by
      rw [Real.sin_pi_div_two_sub]
    linarith
  have eq1 : Real.cos θ - Real.sin θ = Real.sqrt 13 / 6 * (Real.sin θ * Real.cos θ) := by
    have h10 : Real.sin θ ≠ 0 := by linarith
    have h11 : Real.cos θ ≠ 0 := by linarith
    field_simp at h ⊢
    nlinarith

  have eq2 : Real.sin θ * Real.cos θ = 6 / 13 := by
    have h8 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have eq3 : (Real.cos θ - Real.sin θ) ^ 2 = (Real.sqrt 13 / 6 * (Real.sin θ * Real.cos θ)) ^ 2 := by 
      rw [eq1]
    have eq4 : (Real.cos θ - Real.sin θ) ^ 2 = 1 - 2 * (Real.sin θ * Real.cos θ) := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [eq4] at eq3
    have h12 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
    have eq5 : (Real.sqrt 13 / 6 * (Real.sin θ * Real.cos θ)) ^ 2 = (13 / 36) * (Real.sin θ * Real.cos θ) ^ 2 := by
      ring_nf
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
    rw [eq5] at eq3
    have eq6 : Real.sin θ * Real.cos θ = 6 / 13 := by
      nlinarith [sq_nonneg (Real.sin θ * Real.cos θ - 6 / 13), sq_nonneg (Real.sin θ * Real.cos θ + 6), Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
    exact eq6

  have eq34 : Real.cos θ ^ 2 - Real.sin θ ^ 2 = 5 / 13 := by
    have eq4 : Real.cos θ - Real.sin θ = Real.sqrt 13 / 13 := by
      rw [eq2] at eq1
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
    have eq33 : Real.cos θ + Real.sin θ = 5 / Real.sqrt 13 := by
      have eq31 : Real.cos θ + Real.sin θ > 0 := by
        nlinarith
      have eq32 : (Real.cos θ + Real.sin θ) ^ 2 = 25 / 13 := by
        nlinarith [Real.sin_sq_add_cos_sq θ, eq2]
      have h21 : Real.cos θ + Real.sin θ = Real.sqrt (25 / 13) := by
        rw [← eq32]
        field_simp [eq31]
      have h22 : Real.sqrt (25 / 13) = 5 / Real.sqrt 13 := by
        have h23 : Real.sqrt (25 / 13) = Real.sqrt (25) / Real.sqrt (13) := by
          rw [Real.sqrt_div (by norm_num)]
        have h24 : Real.sqrt (25) = (5 : ℝ) := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        rw [h23, h24]
      rw [h22] at h21
      linarith
    have h18 : Real.cos θ ^ 2 - Real.sin θ ^ 2 = (Real.cos θ + Real.sin θ) * (Real.cos θ - Real.sin θ) := by
      nlinarith
    rw [h18, eq33, eq4]
    have h16 : Real.sqrt 13 > 0 := by
      positivity
    field_simp
    all_goals
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]

  have eq36 : 1 / Real.tan θ - Real.tan θ = (Real.cos θ ^ 2 - Real.sin θ ^ 2) / (Real.sin θ * Real.cos θ) := by
    have eq38 : 1 / Real.tan θ = Real.cos θ / Real.sin θ := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    have eq39 : Real.tan θ = Real.sin θ / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos]
    rw [eq38, eq39]
    have h19 : Real.sin θ ≠ 0 := by linarith
    have h20 : Real.cos θ ≠ 0 := by linarith
    field_simp
    all_goals nlinarith

  rw [eq36]
  have eq37 : Real.sin θ * Real.cos θ = 6 / 13 := eq2
  rw [eq34, eq37]
  all_goals
    nlinarith