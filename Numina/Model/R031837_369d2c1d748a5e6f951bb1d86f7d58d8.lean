import Mathlib

theorem algebra_21442 {a b : ℝ} (h₀ : a^2 * b^3 = 32 / 27) (h₁ : a / b^3 = 27 / 4) : a + b = 8 / 3 := by
  have hb : b ≠ 0 := by
    by_contra h
    rw [h] at h₁ 
    norm_num at h₁ 
  have h2 : a = 27 / 4 * b^3 := by
    have h2 : b ^ 3 ≠ 0 := by
      intro h2
      have : b = 0 := by
        have h11 : b ^ 3 = (0 : ℝ) := by linarith
        have h12 : b = 0 := by
          have h111 : b ^ 3 = 0 := by linarith
          simp at h111 ⊢
          all_goals linarith
        exact h12
      contradiction
    field_simp [hb] at h₁ ⊢
    linarith 
  have h3 : a ^ 2 * b ^ 3 = 32 / 27 := h₀
  rw [h2] at h3
  have h5 : b ^ 9 = 512 / 19683 := by
    nlinarith
  have h6 : (b ^ 3) ^ 3 = (8 / 27) ^ 3 := by 
    nlinarith 
  have h8 : b ^ 3 = 8 / 27 := by
    have h6 : (b ^ 3) ^ 3 - (8 / 27) ^ 3 = 0 := by
      linarith 
    have h7 : (b ^ 3 - 8 / 27) * ((b ^ 3) ^ 2 + (b ^ 3) * (8 / 27) + (8 / 27) ^ 2) = 0 := by
      ring_nf at h6 ⊢
      linarith 
    cases' (mul_eq_zero.1 h7) with h8 h9 
    · -- Case where $b^3 - 8/27 = 0$, implying $b^3 = 8/27$
      linarith
    · -- Case where $(b^3)^2 + b^3*(8/27) + (8/27)^2 = 0$.
      nlinarith [sq_nonneg (b ^ 3 + 4 / 27), sq_nonneg (b * (27 : ℝ) * 2)]
  have h9 : b = 2 / 3 := by
    have h10 : (b - 2 / 3) * (b ^ 2 + (b * (2 / 3)) + (4 / 9)) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 h10) with h4 h5
    · -- Case where $b - 2/3 = 0$
      linarith 
    · -- Case where $b^2 + (b*(2/3)) + (4/9) = 0$
      nlinarith [sq_nonneg (b + 1 / 3), sq_nonneg (b^2 + (b * (2 / 3)) + (4 / 9)), sq_nonneg (b * (2 / 3)), sq_nonneg ((b * (2 / 3)) * (b * (2 / 3)))]
  have ha : a = 2 := by
    rw [h2]
    nlinarith [h8, h9]
  linarith [ha, h9]