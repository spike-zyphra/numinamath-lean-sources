import Mathlib

theorem algebra_305084 (x : ℝ) (hx : 0 < x ∧ x < Real.pi / 2) (h : Real.sin x - Real.cos x = Real.pi / 4) :
    ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ Real.tan x + 1 / Real.tan x = a / (b - Real.pi ^ c) := by
  have h1 : 0 < x := hx.1
  have h2 : x < Real.pi / 2 := hx.2
  have h3 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h4 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith
  have eq1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have eq2 : Real.sin x * Real.cos x = (1 - Real.pi ^ 2 / 16) / 2 := by
    have h5 : Real.sin x - Real.cos x = Real.pi / 4 := h
    have h6 : (Real.sin x - Real.cos x) ^ 2 = (Real.pi / 4) ^ 2 := by
      rw [h5]
    have h7 : (Real.sin x - Real.cos x) ^ 2 = Real.sin x ^ 2 - 2 * (Real.sin x * Real.cos x) + Real.cos x ^ 2 := by
      ring
    have h8 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith
  have h5 : Real.tan x + 1 / Real.tan x = (Real.sin x ^ 2 + Real.cos x ^ 2) / (Real.sin x * Real.cos x) := by
    have htan1 : Real.tan x = Real.sin x / Real.cos x := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [htan1]
    field_simp [show Real.sin x ≠ 0 by linarith [h3], show Real.cos x ≠ 0 by linarith [h4]]
    <;> 
      nlinarith [Real.sin_sq_add_cos_sq x]
  rw [h5]
  have h6 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h6]
  use 32, 16, 2
  constructor
  · norm_num  -- a > 0
  constructor
  · norm_num  -- b > 0
  constructor
  · norm_num  -- c > 0
  have eq5 : Real.sin x * Real.cos x = (1 - Real.pi ^ 2 / 16) / 2 := eq2
  have eq6 : (1 : ℝ) / (Real.sin x * Real.cos x) = 32 / (16 - Real.pi ^ 2) := by
    rw [eq5]
    field_simp [(show (16 : ℝ) - Real.pi ^ 2 ≠ 0 by
      nlinarith [Real.pi_gt_three, Real.pi_lt_315]
    )]
    <;> 
      ring_nf
  field_simp [eq6, eq5]
  <;> 
    nlinarith