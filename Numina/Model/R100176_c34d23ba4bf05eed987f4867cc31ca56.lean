import Mathlib

theorem algebra_215403 (a b : ℝ) (ha : ∀ x > 0, ∃! y : ℝ, |(x ^ y - 1) / (x ^ y + 1)| = a ∧ x ^ 2 + y ^ 2 = b) :
    0 < b ∧ b ≤ 1 := by 
  have h1 := ha 1 (by norm_num)
  rcases h1 with ⟨y1, ⟨h1₁, h1₂⟩, h1u⟩
  have ha0 : a = 0 := by
    have h_eq : |((1:ℝ) ^ y1 - 1) / ((1:ℝ) ^ y1 + 1)| = 0 := by
      have h11 : (1:ℝ) ^ y1 = 1 := by
        simp
      rw [h11]
      norm_num
    have h2 := h1₁
    linarith [h_eq, h2]
  have hb1 : b = 1 + y1 ^ 2 := by
    nlinarith
  have h2 := ha 2 (by norm_num)
  rcases h2 with ⟨y2, ⟨h2₁, h2₂⟩, h2u⟩
  have hy2 : y2 = 0 := by
    rw [ha0] at h2₁
    have h_eq1 : |((2:ℝ) ^ y2 - 1) / ((2:ℝ) ^ y2 + 1)| = 0 := by
      linarith
    have h_eq2 : ((2:ℝ) ^ y2 - 1) / ((2:ℝ) ^ y2 + 1) = 0 := by 
      rwa [abs_eq_zero] at h_eq1
    have h_eq3 : (2:ℝ) ^ y2 - 1 = 0 := by
      have h_ne : (2:ℝ) ^ y2 + 1 ≠ 0 := by
        have h1 : (2:ℝ) ^ y2 > 0 := by
          positivity
        linarith
      field_simp at h_eq2 ⊢
      <;> linarith
    have h_eq4 : (2:ℝ) ^ y2 = 1 := by 
      linarith
    have : y2 = 0 := by
      apply_fun (Real.logb (2:ℝ)) at h_eq4
      simp at h_eq4 ⊢
      linarith
    exact this
  have hb2 : b = 4 := by
    rw [hy2] at h2₂
    nlinarith
  have h3 := ha (10:ℝ) (by norm_num)
  rcases h3 with ⟨y3, ⟨h3₁, h3₂⟩, h3u⟩
  have hy3 : y3 = 0 := by
    rw [ha0] at h3₁
    have h_eq1 : |((10:ℝ) ^ y3 - 1) / ((10:ℝ) ^ y3 + 1)| = 0 := by
      linarith
    have h_eq2 : ((10:ℝ) ^ y3 - 1) / ((10:ℝ) ^ y3 + 1) = 0 := by 
      rwa [abs_eq_zero] at h_eq1
    have h_eq3 : (10:ℝ) ^ y3 - 1 = 0 := by
      have h_ne : (10:ℝ) ^ y3 + 1 ≠ 0 := by
        have h1 : (10:ℝ) ^ y3 > 0 := by
          positivity
        linarith
      field_simp at h_eq2 ⊢
      <;> linarith
    have h_eq4 : (10:ℝ) ^ y3 = 1 := by 
      linarith
    have : y3 = 0 := by
      apply_fun (Real.logb (10:ℝ)) at h_eq4
      simp at h_eq4 ⊢
      linarith
    exact this
  have hb3 : b = (10:ℝ) ^ 2 := by
    rw [hy3] at h3₂
    nlinarith
  have hb4 : 0 < b := by nlinarith [hb1, hb2, hb3]
  have hb5 : b ≤ 1 := by
    nlinarith [hb1, hb2, hb3, sq_nonneg (y1), sq_nonneg (y2 - 0), sq_nonneg (10 - 1), sq_nonneg (10 - 2)]
  exact ⟨hb4, hb5⟩