import Mathlib
open Mathlib

theorem algebra_8007 {a b c : ℕ} (h₀ : a = b + 4) (h₁ : b = c + 1) (h₂ : a + b + c = 11) (h₃ : c - 2 = a + b) :
    a = 5 ∧ b = 4 := by 
  omega