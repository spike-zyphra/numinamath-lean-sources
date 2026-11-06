import Mathlib

theorem algebra_137054 {a b c : ℝ} (h₀ : a * b / (a + b) = 2) (h₁ : b * c / (b + c) = 5)
    (h₂ : c * a / (c + a) = 7) :
    a * b * c / (a * b + b * c + c * a) = 140 / 59 := by

  -- Show $a + b ≠ 0$
  have h3 : a + b ≠ 0 := by
    by_contra h
    have h4 : a * b / (a + b) = 0 := by
      rw [h]
      norm_num
    linarith

  -- Show $b + c ≠ 0$
  have h4 : b + c ≠ 0 := by
    by_contra h
    have h5 : b * c / (b + c) = 0 := by
      rw [h]
      norm_num
    linarith

  -- Show $c + a ≠ 0$
  have h5 : c + a ≠ 0 := by
    by_contra h
    have h6 : c * a / (c + a) = 0 := by
      rw [h]
      norm_num
    linarith

  -- Convert h₀ to reciprocal form: $\frac{1}{a} + \frac{1}{b} = \frac{1}{2}$
  have eq1 : 1 / a + 1 / b = 1 / 2 := by
    have h6 : a + b ≠ 0 := h3
    have h7 : a ≠ 0 := by
      by_contra h8
      have h9 : a + b = b := by linarith
      have h10 : a * b / (a + b) = 0 := by
        rw [h9]
        norm_num [h8]
      linarith
    have h8 : b ≠ 0 := by
      by_contra h9
      have h10 : a + b = a := by linarith
      have h11 : a * b / (a + b) = 0 := by
        rw [h10]
        norm_num [h9]
      linarith
    field_simp [h7, h8] at h₀ ⊢
    linarith

  -- Convert h₁ to reciprocal form: $\frac{1}{b} + \frac{1}{c} = \frac{1}{5}$
  have eq2 : 1 / b + 1 / c = 1 / 5 := by
    have h4 : b + c ≠ 0 := h4
    have h7 : b ≠ 0 := by
      by_contra h8
      have h9 : b + c = c := by linarith
      have h10 : b * c / (b + c) = 0 := by
        rw [h9]
        norm_num [h8]
      linarith
    have h8 : c ≠ 0 := by
      by_contra h9
      have h10 : b + c = b := by linarith
      have h11 : b * c / (b + c) = 0 := by
        rw [h10]
        norm_num [h9]
      linarith
    field_simp [h7, h8] at h₁ ⊢
    linarith

  -- Convert h₂ to reciprocal form: $\frac{1}{c} + \frac{1}{a} = \frac{1}{7}$
  have eq3 : 1 / c + 1 / a = 1 / 7 := by
    have h5 : c + a ≠ 0 := h5
    have h7 : c ≠ 0 := by
      by_contra h8
      have h9 : c + a = a := by linarith
      have h10 : c * a / (c + a) = 0 := by
        rw [h9]
        norm_num [h8]
      linarith
    have h8 : a ≠ 0 := by
      by_contra h9
      have h10 : c + a = c := by linarith
      have h11 : c * a / (c + a) = 0 := by
        rw [h10]
        norm_num [h9]
      linarith
    field_simp [h7, h8] at h₂ ⊢
    linarith

  -- Summing the three reciprocal equations and solving for the sum
  have eq4 : 1 / a + 1 / b + 1 / c = 59 / 140 := by
    linarith

  -- Expressing the desired expression using the reciprocal sum
  have eq5 : a * b * c / (a * b + b * c + c * a) = 1 / (1 / a + 1 / b + 1 / c) := by
    have h6 : a ≠ 0 := by
      by_contra h
      have h6 : a + b = b := by linarith
      have h6' : a * b / (a + b) = 0 := by
        rw [h6]
        norm_num [h]
      linarith
    have h7 : b ≠ 0 := by
      by_contra h
      have h6 : a + b = a := by linarith
      have h6' : a * b / (a + b) = 0 := by
        rw [h6]
        norm_num [h]
      linarith
    have h8 : c ≠ 0 := by
      by_contra h
      have h5 : c + a = a := by linarith
      have h6' : c * a / (c + a) = 0 := by
        rw [h5]
        norm_num [h]
      linarith
    field_simp [h6, h7, h8]
    <;> ring

  -- Substituting the value of the reciprocal sum
  rw [eq5, eq4]
  all_goals norm_num