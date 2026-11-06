import Mathlib

theorem algebra_284833 {a b c x : ℝ} (h₀ : a + b + c = 0) (h₁ : a * b * c = -100)
    (h₂ : x = 1 / a + 1 / b + 1 / c) : x > 0 := by

  have ha : a ≠ 0 := by
    by_contra h
    rw [h] at h₁
    -- This leads to 0 * b * c = -100, which is a contradiction
    nlinarith   -- This will detect a contradiction.

  have hb : b ≠ 0 := by
    by_contra h
    rw [h] at h₁
    -- This leads to a * 0 * c = -100, which is a contradiction
    nlinarith

  have hc : c ≠ 0 := by
    by_contra h
    rw [h] at h₁
    -- This leads to a * b * 0 = -100, which is a contradiction
    nlinarith

  have h₃ : x = (a * b + a * c + b * c) / (a * b * c) := by
    rw [h₂]
    have h4 : 1 / a + 1 / b + 1 / c = (a * b + a * c + b * c) / (a * b * c) := by
      field_simp [ha, hb, hc]
      <;> ring
    rw [h4]

  have h₄ : a * b + a * c + b * c < 0 := by
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, h₀]

  have h₅ : (a * b + a * c + b * c) / (a * b * c) > 0 := by
    apply div_pos_of_neg_of_neg
    linarith
    nlinarith

  rw [h₃]
  linarith