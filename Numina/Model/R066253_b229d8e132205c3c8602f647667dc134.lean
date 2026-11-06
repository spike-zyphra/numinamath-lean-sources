import Mathlib

theorem other_308300 (d : ℕ) (h₀ : d = 563) (f : ℕ) (hf : f = 315) :
    d * 1 ≥ f := by
  subst h₀
  subst hf
  all_goals omega