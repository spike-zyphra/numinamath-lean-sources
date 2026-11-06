import Mathlib

theorem algebra_273658 (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) (h : Real.cos (Real.pi / 3) = Real.cos (Real.pi / 4) * Real.cos θ) :
    θ = Real.pi / 4 := by
  have h1 : 0 ≤ θ := by
    have h1 : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
    simp at h1 ⊢
    linarith
  have h2 : θ ≤ Real.pi / 2 := by
    have h2 : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
    simp at h2 ⊢
    linarith
  have h3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  rw [h3, h4] at h
  have h5 : Real.cos θ = Real.sqrt 2 / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]

  have h6 : θ = Real.arccos (Real.cos θ) := by
    rw [Real.arccos_cos]
    all_goals
      linarith [Real.pi_pos]

  rw [h5] at h6

  have h7 : Real.arccos (Real.sqrt 2 / 2) = Real.pi / 4 := by
    have h8 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [←h8]
    apply Real.arccos_cos
    all_goals
      linarith [Real.pi_pos]

  rw [h7] at h6
  linarith