import Mathlib

theorem algebra_159262 {p q r a b c : ℝ} (h₀ : p + q + r = 1) (h₁ : 1 / p + 1 / q + 1 / r = 0) :
    a ^ 2 + b ^ 2 + c ^ 2 = (p * a + q * b + r * c) ^ 2 +
      (q * a + r * b + p * c) ^ 2 + (r * a + p * b + q * c) ^ 2
  := by
  have hp1 : p ≠ 0 := by
    by_contra h
    have hp0 : p = 0 := by linarith
    rw [hp0] at h₁
    rw [hp0] at h₀
    have hp0' : q + r = 1 := by linarith
    by_cases hq0 : q = 0
    · rw [hq0] at h₁
      have hr1 : r = 1 := by linarith
      rw [hr1] at h₁
      norm_num at h₁
    · have hq0' : q ≠ 0 := by
        intro h
        apply hq0
        all_goals linarith
      by_cases hr0 : r = 0
      · rw [hr0] at h₁
        have h2 : q = 1 := by linarith
        rw [h2] at h₁
        norm_num at h₁
      · have h2 : r ≠ 0 := by
          intro h
          apply hr0
          all_goals linarith
        have h3 : r + q = 0 := by
          field_simp [hq0', h2] at h₁
          nlinarith
        have h4 : q + r = 1 := by linarith
        nlinarith
  have hq1 : q ≠ 0 := by
    by_contra h
    have hq0 : q = 0 := by linarith
    rw [hq0] at h₁
    rw [hq0] at h₀
    have hp0' : p + r = 1 := by linarith
    by_cases hp0 : p = 0
    · rw [hp0] at h₁
      have hr1 : r = 1 := by linarith
      rw [hr1] at h₁
      norm_num at h₁
    · have h2 : p ≠ 0 := by
        intro h
        apply hp0
        all_goals linarith
      by_cases hr0 : r = 0
      · rw [hr0] at h₁
        have hp1 : p = 1 := by linarith
        rw [hp1] at h₁
        norm_num at h₁
      · have h3 : r ≠ 0 := by
          intro h
          apply hr0
          all_goals linarith
        have h4 : p + r = 0 := by
          field_simp [h2, h3] at h₁
          nlinarith
        have h5 : p + r = 1 := by linarith
        nlinarith
  have hr1 : r ≠ 0 := by
    by_contra h
    have hr0 : r = 0 := by linarith
    rw [hr0] at h₁
    rw [hr0] at h₀
    have hp0' : p + q = 1 := by linarith
    by_cases hp0 : p = 0
    · rw [hp0] at h₁
      have hq1 : q = 1 := by linarith
      rw [hq1] at h₁
      norm_num at h₁
    · have h2 : p ≠ 0 := by
        intro h
        apply hp0
        all_goals linarith
      by_cases hq0 : q = 0
      · rw [hq0] at h₁
        have hp1 : p = 1 := by linarith
        rw [hp1] at h₁
        norm_num at h₁
      · have h3 : q ≠ 0 := by
          intro h
          apply hq0
          all_goals linarith
        have h4 : p + q = 0 := by
          field_simp [h2, h3] at h₁
          nlinarith
        have h5 : p + q = 1 := by linarith
        nlinarith
  have h3 : p * q + p * r + q * r = 0 := by
    field_simp [hp1, hq1, hr1] at h₁
    nlinarith
  have h4 : p ^ 2 + q ^ 2 + r ^ 2 = 1 := by
    have h5 : p + q + r = 1 := h₀
    have h6 : p * q + p * r + q * r = 0 := h3
    calc
      p ^ 2 + q ^ 2 + r ^ 2 = (p + q + r) ^ 2 - 2 * (p * q + p * r + q * r) := by ring
      _ = 1 ^ 2 - 2 * (0) := by rw [h5, h6]
      _ = (1 : ℝ) := by norm_num
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r)]