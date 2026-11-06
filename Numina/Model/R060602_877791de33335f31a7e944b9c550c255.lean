import Mathlib

theorem algebra_216845 (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (h : 5 * Real.tan θ - 3 = 0) :
    Real.sin θ = 3 / Real.sqrt 34 := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : Real.cos θ > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]

  have htan : Real.tan θ = Real.sin θ / Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos]

  rw [htan] at h
  have h4 : 5 * Real.sin θ = 3 * Real.cos θ := by
    have h5 : Real.cos θ ≠ 0 := by
      linarith
    field_simp [h5] at h ⊢
    linarith

  have h4' : Real.sin θ = 3 / 5 * Real.cos θ := by
    linarith

  have h6 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [h4'] at h6
  have h7 : Real.cos θ ^ 2 = 25 / 34 := by
    linarith

  have h8 : Real.cos θ = 5 / Real.sqrt 34 := by
    have h9 : Real.sqrt 34 ^ 2 = (34 : ℝ) := by
      norm_num [Real.sq_sqrt]
    have h10 : Real.cos θ > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos]

    have h11 : Real.cos θ = Real.sqrt (25 / 34 : ℝ) := by
      have h12 : Real.sqrt (25 / 34 : ℝ) = (Real.sqrt (25 / 34 : ℝ) : ℝ) := by rfl
      have h13 : Real.cos θ ^ 2 = (25 / 34 : ℝ) := by linarith
      have h14 : Real.cos θ = Real.sqrt (25 / 34 : ℝ) := by
        have h15 : Real.sqrt (Real.cos θ ^ 2) = Real.sqrt (25 / 34 : ℝ) := by
          rw [h13]
        have h16 : Real.sqrt (Real.cos θ ^ 2) = Real.cos θ := by
          apply Real.sqrt_sq (by linarith)
        rw [h16] at h15
        linarith
      linarith

    have h12 : Real.sqrt (25 / 34 : ℝ) = 5 / Real.sqrt 34 := by
      have h13 : (25 / 34 : ℝ) = (25 : ℝ) / (34 : ℝ) := by norm_num
      rw [h13]
      have h14 : Real.sqrt ((25 : ℝ) / (34 : ℝ)) = Real.sqrt (25 : ℝ) / Real.sqrt (34 : ℝ) := by
        field_simp [Real.sqrt_div]
      have h15 : Real.sqrt (25 : ℝ) = (5 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h14, h15]

    rw [h12] at h11
    linarith

  rw [h4']
  rw [h8]
  <;> field_simp <;> ring_nf <;> norm_num
  <;> linarith [Real.sqrt_nonneg 34]