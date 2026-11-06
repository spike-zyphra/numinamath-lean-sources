import Mathlib

theorem algebra_296321 {a b : ℝ} (h₀ : a - b = 2) (h₁ : (1 - a)^2 / b - (1 + b)^2 / a = 4) :
    a^5 - b^5 = 82 := by
  have h₂ : a ≠ 0 := by
    by_contra h
    have ha : a = 0 := by linarith
    rw [ha] at h₀ h₁
    have hb : b = -2 := by linarith
    rw [hb] at h₁
    norm_num at h₁
  have h₃ : b ≠ 0 := by
    by_contra h
    have hb : b = 0 := by linarith
    rw [hb] at h₀ h₁
    have ha : a = 2 := by linarith
    rw [ha] at h₁
    norm_num at h₁

  -- Multiply the equation by a * b to clear denominators
  have h₄ : a * (1 - a)^2 - b * (1 + b)^2 = 4 * a * b := by
    have hx : a ≠ 0 := h₂
    have hy : b ≠ 0 := h₃
    have h₆ : (1 - a)^2 / b - (1 + b)^2 / a = 4 := h₁
    have eq1 : a * (1 - a)^2 - b * (1 + b)^2 = 4 * a * b := by
      have eq3 : (1 - a)^2 / b - (1 + b)^2 / a = (a * (1 - a)^2 - b * (1 + b)^2) / (a * b) := by 
        field_simp [hx, hy]
        <;> ring
      rw [eq3] at h₆
      have h₇ : a * (1 - a)^2 - b * (1 + b)^2 = 4 * a * b := by
        have hx5 : a * b ≠ 0 := mul_ne_zero hx hy
        field_simp [hx5] at h₆ ⊢
        nlinarith
      linarith 
    linarith
  have h₈ : a = b + 2 := by linarith
  rw [h₈] at h₄

  have h2 : b ^ 2 + 2 * b - 1 = 0 := by 
    nlinarith

  have ha2 : a ^ 5 - b ^ 5 = 82 := by 
    have ha1 : a = b + 2 := by linarith 
    rw [ha1]
    nlinarith [sq_nonneg (b ^ 2 - 1 ), sq_nonneg (b * (b + 1 ) ) ]
  linarith