import Mathlib

theorem algebra_313212 {k : ℝ} (hk : k > 0) (x₁ x₂ : ℝ)
    (h₁ : x₁ * k + 1 = k / x₁) (h₂ : x₂ * k + 1 = k / x₂)
    (h₃ : |x₁ - x₂| = Real.sqrt 5) :
    k = 1 := by
  have h1₁ : x₁ ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁
    all_goals linarith
  have h1₂ : x₂ ≠ 0 := by
    by_contra h
    rw [h] at h₂
    norm_num at h₂
    all_goals linarith
  have h4 : k * x₁^2 + x₁ - k = 0 := by
    have h5 : x₁ ≠ 0 := h1₁
    field_simp at h₁
    linarith
  have h5 : k * x₂^2 + x₂ - k = 0 := by
    have h6 : x₂ ≠ 0 := h1₂
    field_simp at h₂
    linarith
  have h6 : (x₁ - x₂) * (k * (x₁ + x₂) + 1) = 0 := by
    nlinarith [h4, h5]
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- If x₁ - x₂ = 0, then |x₁ - x₂| = 0, contradiction
    have h7' : x₁ - x₂ = 0 := by linarith
    have h8' : x₁ = x₂ := by linarith
    have h9 : |x₁ - x₂| = 0 := by
      rw [h8']
      norm_num
    rw [h9] at h₃
    have h10 : Real.sqrt 5 > 0 := by
      positivity
    linarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0)]
  · -- Case where k*(x₁ + x₂) + 1 = 0, meaning k*(x₁ + x₂) = -1
    have h7 : k * (x₁ + x₂) = -1 := by linarith
    have h8 : x₁ * x₂ = -1 := by
      nlinarith [h4, h5, sq_pos_of_pos hk, sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_pos_of_ne_zero (show k ≠ 0 by linarith)]
    have h9 : (x₁ - x₂) ^ 2 = 5 := by
      calc
        (x₁ - x₂) ^ 2 = (Real.sqrt 5) ^ 2 := by
          rw [<-h₃]
          all_goals norm_num
        _ = 5 := Real.sq_sqrt (by norm_num)
    have h10 : (x₁ - x₂) ^ 2 = (x₁ + x₂) ^ 2 - 4 * (x₁ * x₂) := by
      nlinarith
    rw [h8] at h10
    have h12 : (x₁ + x₂) = -1 / k := by
      field_simp at h7 ⊢
      nlinarith
    rw [h12] at h10
    have h13 : k = 1 := by
      field_simp at h10
      nlinarith [h9, sq_nonneg (k - 1), sq_nonneg (k + 1)]
    linarith