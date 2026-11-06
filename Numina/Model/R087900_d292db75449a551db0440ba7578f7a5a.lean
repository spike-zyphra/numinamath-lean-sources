import Mathlib

theorem algebra_307315 (a b c d e f : ℝ)
    (h₀ : 2 * a + b + c + d + e + f = 20)
    (h₁ : a + 2 * b + c + d + e + f = 40)
    (h₂ : a + b + 2 * c + d + e + f = 80)
    (h₃ : a + b + c + 2 * d + e + f = 160)
    (h₄ : a + b + c + d + 2 * e + f = 320)
    (h₅ : a + b + c + d + e + 2 * f = 640) :
    f - e + d - c + b - a = 420 := by 
  linarith