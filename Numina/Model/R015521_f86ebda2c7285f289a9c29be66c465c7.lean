import Mathlib

theorem algebra_310667 (x : ℝ) (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (h : x^2 + 2 * x * Real.cos θ = Real.sin θ - 5 / 4) :
    (x + Real.tan θ) / (x - Real.tan θ) = 1 / 5 := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : 0 < θ := h1
  have h4 : θ < Real.pi / 2 := h2
  have h5 : Real.sin θ > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [h3, Real.pi_pos]
    linarith [h4, Real.pi_pos]
  have h6 : Real.cos θ > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [h3, Real.pi_pos]
    linarith [h4, Real.pi_pos]
  have h7 : Real.sin θ = 1 / 2 := by
    nlinarith [sq_nonneg (x + Real.cos θ), sq_nonneg (Real.sin θ - 1 / 2), Real.sin_sq_add_cos_sq θ, sq_nonneg (x + Real.cos θ), sq_nonneg (Real.cos θ * 2 + Real.sin θ * 2), h5, h6, sq_nonneg (2 * Real.cos θ ^ 2 - 2 * Real.sin θ + 2 * Real.cos θ ^ 2), sq_nonneg (x - (-Real.cos θ)), sq_nonneg (Real.cos θ ^ 2 - 3 / 4)]
  have h9 : Real.cos θ = Real.sqrt 3 / 2 := by
    have h10 : Real.cos θ > 0 := h6
    have h11 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h7] at h11
    have h12 : Real.cos θ ^ 2 = 3 / 4 := by nlinarith
    have h13 : Real.cos θ = Real.sqrt (3 / 4) := by
      rw [← h12]
      field_simp [h10]
    rw [h13]
    have h14 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    exact h14
  have htan : Real.tan θ = 1 / Real.sqrt 3 := by
    rw [Real.tan_eq_sin_div_cos, h7, h9]
    field_simp
  have hx : x = -Real.cos θ := by
    nlinarith [sq_nonneg (x + Real.cos θ), Real.sin_sq_add_cos_sq θ, h5, h6, h7, h9]
  rw [hx, htan, h9]
  field_simp [h5, h6, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  <;> ring_nf <;> norm_num
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3: ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3: ℝ) by norm_num)]