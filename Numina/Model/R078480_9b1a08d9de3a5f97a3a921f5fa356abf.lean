import Mathlib

theorem number_theory_234427 :
    ∃ x y z : ℕ, 28*x+30*y+31*z=365 := by
  exact ⟨1, 4, 7, by norm_num⟩