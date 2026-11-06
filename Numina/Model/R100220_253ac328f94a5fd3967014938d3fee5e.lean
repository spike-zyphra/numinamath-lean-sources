import Mathlib

theorem algebra_7926 {a b c x : ℚ} (h₀ : a = -b) (h₁ : abs b = c) (h₂ : a = x + 2) (h₃ : c = 8 - 2 * x) :
    x = 2 := by 
  have hb : b = -(x + 2) := by 
    linarith [h₀, h₂]
  rw [hb] at h₁ 
  rw [h₃] at h₁
  have h : abs (-(x + 2) : ℚ) = abs (x + 2 : ℚ) := by 
    rw [abs_neg]
  rw [h] at h₁ 
  cases le_or_lt 0 (x + 2) with 
  | inl h4 =>
    rw [abs_of_nonneg h4] at h₁ 
    linarith 
  | inr h5 =>
    rw [abs_of_neg h5] at h₁ 
    linarith