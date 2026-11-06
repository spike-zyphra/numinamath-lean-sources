import Mathlib

theorem algebra_146875 {a b : ℝ} (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * Real.tan x ^ 3 + b * Real.sin x + 1)
    (h₁ : f 4 = 5) : f (2 * Real.pi - 4) = -3 := by
  have eq1 : f 4 = a * Real.tan 4 ^ 3 + b * Real.sin 4 + 1 := h₀ 4 
  have eq2 : f (2 * Real.pi - 4) = a * Real.tan (2 * Real.pi - 4) ^ 3 + b * Real.sin (2 * Real.pi - 4) + 1 := h₀ (2 * Real.pi - 4)
  have h2 : Real.sin (2 * Real.pi - 4) = - Real.sin 4 := by 
    rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
    ring
  have h3 : Real.tan (2 * Real.pi - 4) = - Real.tan 4 := by 
    have htan1 : Real.tan (2 * Real.pi - 4) = Real.sin (2 * Real.pi - 4) / Real.cos (2 * Real.pi - 4) := by 
      rw [Real.tan_eq_sin_div_cos]
    have htan2 : Real.tan 4 = Real.sin 4 / Real.cos 4 := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [htan1, htan2]
    have hcos : Real.cos (2 * Real.pi - 4) = Real.cos 4 := by 
      rw [Real.cos_sub, Real.sin_two_pi, Real.cos_two_pi]
      ring
    rw [h2, hcos]
    <;> ring
  rw [eq2]
  rw [h3, h2]
  have eq3 : a * Real.tan 4 ^ 3 + b * Real.sin 4 = 4 := by
    linarith [h₁, eq1]
  nlinarith [sq_nonneg (Real.tan 4 ^ 2 - (Real.sin 4) ^ 2), sq_nonneg (a - b), sq_nonneg (Real.tan 4 * Real.sin 4), sq_nonneg (b)]