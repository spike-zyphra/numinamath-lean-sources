import Mathlib

theorem number_theory_17099 (A B C : ℕ) (h : A < 12) (h' : B < 60) (h'' : C < 60)(h' : A = 122 % 12) (h' : B = 39 % 60) (h'' : C = 44 % 60):
  A + B + C = 85 := by
    omega