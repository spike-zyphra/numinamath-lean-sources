import Mathlib

theorem calculus_184605 (h c : ℕ) (h₀ : h = 2) (h₁ : c = 3) :
    h * 4 + c * 2 - (h + c) = 9 := by 
  subst h₀
  subst h₁
  all_goals norm_num