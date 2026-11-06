import Mathlib

theorem algebra_164443 {a b c d : ℝ} (h₀ : a + b = c + d) (h₁ : c + d ≠ 0)
    (h₂ : a * c = b * d) : a + c = b + d := by
  have h3 : b = c + d - a := by
    linarith
  rw [h3] at h₂
  have h4 : a * (c + d) = d * (c + d) := by
    linarith [h₂]
  have ha : a = d := by
    apply (mul_left_inj' h₁).mp
    linarith [h4]
  have hb : b = c := by
    rw [ha] at h₀
    linarith
  linarith [ha, hb]