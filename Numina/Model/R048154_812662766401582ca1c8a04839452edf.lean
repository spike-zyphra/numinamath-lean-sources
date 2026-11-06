import Mathlib

theorem algebra_123331 {a b s t : ℝ} (h₀ : s ≠ t) (h₁ : s^2 + a * s + b = t)
    (h₂ : t^2 + a * t + b = s) :
    (b - s * t)^2 + a * (b - s * t) + b - s * t = 0 := by
  have h3 : (s - t) * (s + t + a + 1) = 0 := by
    have h4 : s^2 + a * s + b - (t^2 + a * t + b) = t - s := by linarith
    have h5 : s^2 + a * s + b - (t^2 + a * t + b) = (s^2 - t^2) + a * (s - t) := by linarith
    have h6 : (s^2 - t^2) + a * (s - t) = (s - t) * (s + t + a) := by
      ring
    have h7 : t - s = - (s - t) := by linarith
    have h8 : (s - t) * (s + t + a) = - (s - t) := by
      nlinarith [h4, h5, h6, h7]
    have h9 : (s - t) * (s + t + a + 1) = 0 := by
      linarith
    linarith
  have h4 : s + t + a + 1 = 0 := by
    apply (mul_left_inj' (show s - t ≠ 0 by
      intro h
      apply h₀
      linarith
    )).mp
    linarith
  have ha : a = -1 - s - t := by linarith
  have hb : b = s + t + s * t := by
    rw [ha] at h₁
    nlinarith
  have h5 : b - s * t = s + t := by
    nlinarith [hb]
  rw [h5, ha]
  nlinarith [hb]