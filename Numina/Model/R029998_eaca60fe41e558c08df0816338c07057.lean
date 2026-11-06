import Mathlib

theorem algebra_9677 (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) (h : Real.cos θ - Real.sin θ = Real.sqrt (34) / 17) : Real.tan θ = 3 / 5 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  have h1 : Real.cos θ ≥ 0 := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith
  have h2 : Real.sin θ ≥ 0 := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    linarith
    linarith
  have h3 : (Real.cos θ - Real.sin θ) ^ 2 = (Real.sqrt 34 / 17) ^ 2 := by
    rw [h]
  have h4 : (Real.sqrt 34 / 17 : ℝ) ^ 2 = (34 : ℝ) / 289 := by
    calc
      (Real.sqrt 34 / 17 : ℝ) ^ 2 = (Real.sqrt 34) ^ 2 / (289 : ℝ) := by ring_nf
      _ = (34 : ℝ) / (289 : ℝ) := by 
        rw [Real.sq_sqrt]
        all_goals norm_num
  have h5 : (34 : ℝ) / 289 = (2 : ℝ) / 17 := by norm_num
  have h6 : (Real.cos θ - Real.sin θ) ^ 2 = Real.cos θ ^ 2 + Real.sin θ ^ 2 - 2 * (Real.sin θ * Real.cos θ) := by
    ring
  have h7 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have h8 : Real.sin θ * Real.cos θ = 15 / 34 := by
    nlinarith
  have h9 : (Real.sin θ + Real.cos θ) ^ 2 = 32 / 17 := by
    nlinarith
  have h10 : Real.sin θ + Real.cos θ = 4 * Real.sqrt 34 / 17 := by
    have h9' : (Real.sin θ + Real.cos θ) ^ 2 = 32 / 17 := by linarith 
    have h9'' : 0 ≤ Real.sin θ + Real.cos θ := by nlinarith 
    have h11 : Real.sin θ + Real.cos θ = Real.sqrt (32 / 17) := by
      rw [←h9']
      field_simp 
      <;> nlinarith
    have h12 : Real.sqrt (32 / 17) = 4 * Real.sqrt 34 / 17 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num [mul_add, mul_comm]
      <;> ring 
      <;> norm_num
    rw [h12] at h11 
    linarith
  have h13 : Real.sin θ = 3 * Real.sqrt 34 / 34 := by
    nlinarith [sq_nonneg (Real.sin θ - 0), sq_nonneg (Real.cos θ - 0)]
  have h14 : Real.cos θ = 5 * Real.sqrt 34 / 34 := by
    nlinarith [sq_nonneg (Real.sin θ - 0), sq_nonneg (Real.cos θ - 0)]
  have h15 : Real.tan θ = Real.sin θ / Real.cos θ := by 
    rw [Real.tan_eq_sin_div_cos]
  rw [h15]
  rw [h13, h14]
  <;> field_simp
  <;> nlinarith [Real.sqrt_pos.mpr (show (34 : ℝ) > 0 by norm_num : (34 : ℝ) > (0 : ℝ)), Real.mul_self_sqrt (show (0 : ℝ) ≤ (34 : ℝ) by norm_num : (0 : ℝ) ≤ (34 : ℝ))]