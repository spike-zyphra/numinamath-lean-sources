import Mathlib

theorem algebra_173317 (θ : Real) (hθ : θ ∈ Set.Ioo 0 Real.pi) (h : Real.sin θ + Real.cos θ = 1 / 5) :
    Real.tan θ = -4 / 3 := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : Real.sin θ > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [h1, h2]
    linarith [h1, h2]
  have h4 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h5 : (Real.sin θ + Real.cos θ) ^ 2 = (1 / 5) ^ 2 := by
    rw [h]
  have h6 : (Real.sin θ + Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 + 2 * (Real.sin θ * Real.cos θ) := by
    ring
  rw [h6] at h5
  have h7 : Real.sin θ * Real.cos θ = -12 / 25 := by
    nlinarith [h4, h5]
  have h8 : Real.sin θ = 4 / 5 := by
    have h9 : Real.sin θ > 0 := h3
    have h10 : Real.sin θ = 4 / 5 := by
      nlinarith [h, h7, sq_pos_of_pos h9, sq_nonneg (Real.sin θ - 4 / 5), sq_nonneg (Real.sin θ + 3 / 5)]
    exact h10
  have h9 : Real.sin θ = 4 / 5 := h8
  have h10 : Real.cos θ = -3 / 5 := by
    nlinarith [h, h9]
  rw [Real.tan_eq_sin_div_cos]
  rw [h9, h10]
  all_goals norm_num