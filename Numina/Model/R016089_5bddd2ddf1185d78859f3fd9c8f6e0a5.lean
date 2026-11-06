import Mathlib

theorem algebra_200133 (θ : ℝ) (hθ : Real.tan θ = 5 / 12) (hθ1 : 180 * Real.pi / 180 ≤ θ ∧ θ ≤ 270 * Real.pi / 180) :
    Real.cos θ + Real.sin θ = -17 / 13 := by
  have h1 : Real.cos θ ≠ 0 := by
    by_contra h
    have htan : Real.tan θ = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    linarith [hθ, htan]
  have h2 : Real.sin θ = 5 / 12 * Real.cos θ := by
    have htan : Real.tan θ = Real.sin θ / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan] at hθ
    have h3 : Real.cos θ ≠ 0 := h1
    field_simp [h3] at hθ ⊢
    linarith
  have h3 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [show Real.sin θ = 5 / 12 * Real.cos θ by linarith [h2]] at h3
  have h4 : Real.cos θ ^ 2 = 144 / 169 := by
    nlinarith
  have h5 : Real.pi ≤ θ := by
    nlinarith [hθ1.1, Real.pi_pos]
  have h6 : θ ≤ 3 * Real.pi / 2 := by
    nlinarith [hθ1.2, Real.pi_pos]
  have h7 : Real.cos θ ≤ 0 := by
    apply Real.cos_nonpos_of_pi_div_two_le_of_le
    all_goals
    nlinarith [Real.pi_pos, h5, h6]
  have h8 : Real.cos θ < 0 := by
    by_contra h
    push_neg at h
    have h9 : Real.cos θ = 0 := by
      nlinarith [h7, h, h4]
    contradiction
  have h9 : Real.cos θ = -12 / 13 := by
    nlinarith [h4, h7, h8]
  have h10 : Real.sin θ = -5 / 13 := by
    rw [h9] at h2
    linarith
  rw [h9, h10]
  all_goals norm_num