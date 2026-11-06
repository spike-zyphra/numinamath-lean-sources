import Mathlib

theorem algebra_15431 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : 120 = (1/2) * a * b) (h₅ : a = 24) :
    a + b + c = 60 := by

  have ha : a = 24 := h₅
  have hb : b = 10 := by
    rw [ha] at h₄
    nlinarith

  have hc : c = 26 := by
    rw [ha, hb] at h₃
    nlinarith

  rw [ha, hb, hc]
  all_goals norm_num