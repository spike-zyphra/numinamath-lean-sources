import Mathlib


theorem algebra_244587 {a b c d : ℝ} (h₀ : a + c = -1) (h₁ : a * c + b + d = -1)
    (h₂ : a * d + b * c = -5) (h₃ : b * d = 6) :
    (a = -3 ∧ b = 2 ∧ c = 2 ∧ d = 3) ∨ (a = 2 ∧ b = 3 ∧ c = -3 ∧ d = 2) := by

  have h4 : c = -1 - a := by linarith

  rw [h4] at h₁
  have h5 : -a^2 - a + b + d = -1 := by
    nlinarith

  rw [h4] at h₂
  -- Now solving system
  have h9 : (a + 3) * (a - 2) = 0 := by
    nlinarith [sq_nonneg (a + 3), sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (b - 3), sq_nonneg (d - 3), sq_nonneg (d - 2)]

  cases' (mul_eq_zero.1 h9) with h9 h9
  · -- a = -3 for factor.
    have ha : a = -3 := by linarith
    have h10 : b + d = 5 := by
      rw [ha] at h5
      nlinarith
    have h11 : b * d = 6 := by
      nlinarith
    have h12 : (b - 2) * (b - 3) = 0 := by
      nlinarith [sq_nonneg (b - 2), sq_nonneg (b - 3)]
    cases' (mul_eq_zero.1 h12) with h13 h13
    · -- b = 2
      have hb : b = 2 := by linarith
      have hc : c = 2 := by
        nlinarith [ha, h4]
      have hd : d = 3 := by
        nlinarith [hb, h10]
      left
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · -- b = 3
      have hb : b = 3 := by linarith
      -- invalid.
      nlinarith
  · -- a = 2
    have ha : a = 2 := by linarith
    have h10 : b + d = 5 := by
      rw [ha] at h5
      nlinarith
    have h11 : b * d = 6 := by
      nlinarith
    have h12 : (b - 2) * (b - 3) = 0 := by
      nlinarith [sq_nonneg (b - 2), sq_nonneg (b - 3)]
    cases' (mul_eq_zero.1 h12) with h13 h13
    · -- b = 2
      have hb : b = 2 := by linarith
      -- invalid.
      nlinarith
    · -- b = 3
      have hb : b = 3 := by linarith
      have hc : c = -3 := by
        nlinarith [ha, h4]
      have hd : d = 2 := by
        nlinarith [hb, h10]
      right
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩