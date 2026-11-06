import Mathlib

theorem algebra_206409 {θ : ℝ} (hθ : 0 < θ ∧ θ < Real.pi) (x : ℝ)
    (hx : x ≠ 0) (h : x + 1 / x = 2 * Real.cos θ) (n : ℕ) (hn : n > 0) :
    x ^ n + 1 / x ^ n = 2 * Real.cos (n * θ) := by
  have h1 : x + 1 / x = 2 * Real.cos θ := h
  have h2 : x > 0 ∨ x < 0 := by
    by_contra h'
    push_neg at h'
    have : x = 0 := by linarith
    contradiction
  rcases h2 with (hx1 | hx2)
  · -- x > 0
    have h3 : x + 1 / x ≥ 2 := by
      have h4 : x > 0 := hx1
      have h5 : x + 1 / x - 2 ≥ 0 := by
        have h6 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
          field_simp
          ring
        rw [h6]
        have h7 : (x - 1) ^ 2 ≥ 0 := by
          exact sq_nonneg (x - 1)
        have h8 : (x - 1) ^ 2 / x ≥ 0 := by
          apply div_nonneg
          · linarith
          all_goals linarith
        linarith
      linarith
    have h9 : 2 * Real.cos θ < 2 := by
      have h11 : Real.cos θ < 1 := by
        have h12 : θ > 0 := hθ.1
        have h13 : θ < Real.pi := hθ.2
        have h14 : Real.cos θ < Real.cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [h12, Real.pi_pos]
        have h15 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
        linarith [h14, h15]
      linarith
    nlinarith [h3, h9]
  · -- x < 0
    have h3 : x + 1 / x ≤ -2 := by
      have h4 : x < 0 := hx2
      have h5 : x + 1 / x + 2 ≤ 0 := by
        have h6 : x + 1 / x + 2 = (x + 1) ^ 2 / x := by
          field_simp
          ring
        rw [h6]
        have h7 : (x + 1) ^ 2 ≥ 0 := by
          exact sq_nonneg (x + 1)
        have h8 : (x + 1) ^ 2 / x ≤ 0 := by
          apply div_nonpos_of_nonneg_of_nonpos
          · linarith
          all_goals linarith
        linarith
      linarith
    have h9 : 2 * Real.cos θ > -2 := by
      have h11 : Real.cos θ > -1 := by
        have h12 : θ > 0 := hθ.1
        have h13 : θ < Real.pi := hθ.2
        have h14 : Real.sin θ > 0 := by
          apply Real.sin_pos_of_pos_of_lt_pi
          all_goals linarith
        have h15 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
        nlinarith [Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2, Real.sin_sq_le_one θ, Real.cos_sq_le_one θ]
      linarith
    nlinarith [h3, h9]