import Mathlib

theorem algebra_11390 (x : ℝ) (hx : 0 < x ∧ x < Real.pi / 2)
    (h : (Real.sin x)^4 / 9 + (Real.cos x)^4 / 4 = 1 / 13) :
    Real.tan x = 3 / 2 := by
  have hx1 : 0 < x := hx.1
  have hx2 : x < Real.pi / 2 := hx.2
  have h1 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    all_goals
    linarith
  have h2 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    all_goals
    linarith
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have eq1 : (Real.sin x) ^ 4 = (Real.sin x ^ 2) ^ 2 := by ring
  have eq2 : (Real.cos x) ^ 4 = (Real.cos x ^ 2) ^ 2 := by ring
  rw [eq1, eq2] at h
  have h5 : Real.sin x ^ 2 = 9 / 13 := by
    nlinarith [sq_nonneg (Real.sin x ^ 2 - 9 / 13), sq_nonneg (Real.cos x ^ 2 - 4 / 13),
      h1, h2, h3]
  have h8 : Real.cos x ^ 2 = 4 / 13 := by
    nlinarith [sq_nonneg (Real.sin x ^ 2 - 9 / 13), sq_nonneg (Real.cos x ^ 2 - 4 / 13),
      h1, h2, h3, h5]
  have h7 : Real.sin x = Real.sqrt (9 / 13) := by
    have h10 : Real.sin x ^ 2 = 9 / 13 := h5
    have h11 : Real.sin x = Real.sqrt (Real.sin x ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      have : Real.sin x ≥ 0 := by linarith
      rw [abs_of_nonneg this]
    rw [h10] at h11
    linarith
  have h9 : Real.sqrt (9 / 13) = 3 / Real.sqrt 13 := by
    have h10 : Real.sqrt (9 / 13) = Real.sqrt 9 / Real.sqrt 13 := by
      rw [Real.sqrt_div]
      all_goals
      norm_num
    have h11 : Real.sqrt 9 = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h10, h11]
    all_goals
    norm_num
  have h9' : Real.sin x = 3 / Real.sqrt 13 := by
    rw [h7, h9]
    all_goals
    norm_num
  have h10 : Real.cos x = Real.sqrt (4 / 13) := by
    have h11 : Real.cos x ^ 2 = 4 / 13 := h8
    have h12 : Real.cos x = Real.sqrt (Real.cos x ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      have : Real.cos x ≥ 0 := by linarith
      rw [abs_of_nonneg this]
    rw [h11] at h12
    linarith
  have h11' : Real.sqrt (4 / 13) = 2 / Real.sqrt 13 := by
    have h12 : Real.sqrt (4 / 13) = Real.sqrt 4 / Real.sqrt 13 := by
      rw [Real.sqrt_div]
      all_goals
      norm_num
    have h13 : Real.sqrt 4 = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h12, h13]
    all_goals
    norm_num
  have h10' : Real.cos x = 2 / Real.sqrt 13 := by
    rw [h10, h11']
    all_goals
    norm_num
  have h12 : Real.tan x = 3 / 2 := by
    rw [Real.tan_eq_sin_div_cos]
    rw [h9', h10']
    field_simp
    all_goals
    ring_nf <;> field_simp
    all_goals
    linarith
  exact h12