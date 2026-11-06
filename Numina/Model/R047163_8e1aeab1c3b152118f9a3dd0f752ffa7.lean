import Mathlib

theorem algebra_324938 (θ : ℝ) (hθ : θ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) (h : Real.sin θ + Real.cos θ = 1 / 3) :
    θ = -Real.arcsin ((Real.sqrt 17 - 1) / 6) := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h4 : Real.cos θ = 1 / 3 - Real.sin θ := by linarith
  rw [h4] at h3
  have h5 : Real.sin θ ^ 2 + (1 / 3 - Real.sin θ) ^ 2 = 1 := by nlinarith
  have h6 : Real.sin θ = (1 - Real.sqrt 17) / 6 ∨ Real.sin θ = (1 + Real.sqrt 17) / 6 := by
    have h7 : 18 * (Real.sin θ) ^ 2 - 6 * (Real.sin θ) - 8 = 0 := by
      nlinarith
    have h8 : (Real.sin θ - (1 - Real.sqrt 17) / 6) * (Real.sin θ - (1 + Real.sqrt 17) / 6) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    cases' (mul_eq_zero.1 h8) with h9 h10
    · left
      linarith
    · right
      linarith
  cases h6 with
  | inl h7 =>
    -- sin θ = (1 - Real.sqrt 17) / 6
    have h8 : Real.sin θ = (1 - Real.sqrt 17) / 6 := h7
    have h9 : θ = Real.arcsin (Real.sin θ) := by
      rw [Real.arcsin_sin]
      all_goals
        linarith [Real.pi_pos]
    rw [h9, h8]
    have h10 : Real.arcsin ((1 - Real.sqrt 17) / 6) = - Real.arcsin ((Real.sqrt 17 - 1) / 6) := by
      have h11 : (1 - Real.sqrt 17) / 6 = - ((Real.sqrt 17 - 1) / 6) := by
        ring_nf
      rw [h11]
      have h12 : Real.arcsin (- ((Real.sqrt 17 - 1) / 6)) = - Real.arcsin ((Real.sqrt 17 - 1) / 6) := by
        rw [show - ((Real.sqrt 17 - 1) / 6) = -((Real.sqrt 17 - 1) / 6) by ring]
        rw [Real.arcsin_neg]
      linarith [h12]
    linarith [h10]
  | inr h7 =>
    -- sin θ = (1 + Real.sqrt 17) / 6
    -- This gives cos θ < 0, which is invalid in (-π/2, π/2)
    have h8 : Real.sin θ = (1 + Real.sqrt 17) / 6 := h7
    have h9 : Real.cos θ = (1 - Real.sqrt 17) / 6 := by
      linarith [h8, show Real.cos θ = 1 / 3 - Real.sin θ by linarith]
    have h10 : Real.cos θ > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos, h1]
      · linarith [Real.pi_pos, h2]
    nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]