import Mathlib

theorem algebra_3224 (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) (h : 7 * (Real.cos θ)^2 + 11 * Real.sin θ * Real.cos θ = 3) :
    Real.tan θ = 4 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  have h1 : Real.sin θ ≥ 0 := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : Real.cos θ ≥ 0 := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h3 : Real.cos θ > 0 := by
    by_contra h4
    have h4' : Real.cos θ = 0 := by linarith
    have h5 : Real.sin θ = 1 := by
      have h6 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
      rw [h4'] at h6
      nlinarith
    rw [h4', h5] at h
    nlinarith
  have htan2 : 3 * (Real.tan θ) ^ 2 - 11 * Real.tan θ - 4 = 0 := by
    have htan : Real.tan θ = Real.sin θ / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan]
    field_simp [show Real.cos θ ≠ 0 by linarith]
    have h3' : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg (Real.sin θ ^ 2 - 16/9), sq_nonneg (Real.sin θ ^ 2 - (1 - Real.cos θ ^ 2)), sq_nonneg (Real.sin θ - 3 * Real.cos θ / 4 * 1), sq_nonneg ((4/3) * Real.sin θ / 1)]
  have htan3 : (Real.tan θ - 4) * (Real.tan θ + (1 / 3)) = 0 := by
    nlinarith [htan2]
  cases' (mul_eq_zero.mp htan3) with htan4 htan5
  · -- Real.tan θ - 4 = 0
    linarith
  · -- Real.tan θ + 1/3 = 0
    have : Real.tan θ ≥ 0 := by
      apply Real.tan_nonneg_of_nonneg_of_le_pi_div_two
      linarith
      linarith
    nlinarith