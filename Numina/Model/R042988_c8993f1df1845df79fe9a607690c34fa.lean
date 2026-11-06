import Mathlib

theorem algebra_163299 {a b : ℝ} (ha : a * b = 5) (hb : 1 / a ^ 2 + 1 / b ^ 2 = 0.6) :
    a + b = 5 ∨ a + b = -5 := by

  have h1 : a ≠ 0 := by
    by_contra h
    have h2 : a * b = 0 := by
      rw [h]
      norm_num
    linarith

  have h2 : b ≠ 0 := by
    by_contra h
    have h3 : a * b = 0 := by
      rw [h]
      norm_num
    linarith

  have h3 : 1 / a ^ 2 + 1 / b ^ 2 = (a^2 + b^2) / (a * b) ^ 2 := by
    field_simp [h1, h2]
    <;> ring

  rw [h3] at hb

  have h4 : (a * b) ^ 2 = 25 := by
    have h5 : a * b = 5 := by
      linarith
    rw [h5]
    norm_num

  have h6 : a^2 + b^2 = 15 := by
    have h7 : (a * b) ^ 2 = 25 := h4
    have h8 : (a^2 + b^2) / (a * b) ^ 2 = (0.6 : ℝ) := by
      simpa using hb
    rw [h7] at h8
    have h9 : (a^2 + b^2) / (25 : ℝ) = (0.6 : ℝ) := by
      simpa using h8
    norm_num at h9 ⊢
    linarith

  have h7 : (a + b) ^ 2 = 25 := by
    nlinarith [ha, h6]

  have h8 : a + b = 5 ∨ a + b = -5 := by
    have h9 : (a + b) ^ 2 - 25 = 0 := by
      linarith
    have h10 : (a + b - 5) * (a + b + 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case 1
      left
      linarith
    · -- Case 2
      right
      linarith

  exact h8