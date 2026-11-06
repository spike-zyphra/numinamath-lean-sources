import Mathlib

open Polynomial

theorem algebra_18728 (a b c : ℝ) (f : ℝ → ℝ)
    (h₀ : f = fun x => x ^ 4 + a * x ^ 2 + b * x + c)
    (h₁ : f 2 = 0) (h₂ : f (-3) = 0) (h₃ : f 5 = 0) :
    a + b + c = 79 := by
  have eq1 : 2^4 + a * 2^2 + b * 2 + c = 0 := by
    rw [h₀] at h₁
    simpa using h₁
  have eq2 : (-3)^4 + a * (-3)^2 + b * (-3) + c = 0 := by
    rw [h₀] at h₂
    simpa using h₂
  have eq3 : 5^4 + a * 5^2 + b * 5 + c = 0 := by
    rw [h₀] at h₃
    simpa using h₃
  norm_num at eq1 eq2 eq3
  linarith