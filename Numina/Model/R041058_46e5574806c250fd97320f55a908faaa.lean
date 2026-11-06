import Mathlib

theorem number_theory_177148 (n : ℕ) (h₀ : n ≠ 0) (h₁ : (n / 9 : ℝ) * 75 / 100 + 6 = n / 10) :
    n = 360 := by
  have eq1 : (n : ℝ) > 0 := by
    by_contra h
    push_neg at h
    have h2 : (n : ℝ) = 0 := by linarith
    have h3 : n = 0 := by exact_mod_cast (show (n : ℝ) = 0 by linarith)
    contradiction
  have eq2 : (n : ℝ) = 360 := by
    linarith
  have eq3 : n = 360 := by
    exact_mod_cast eq2
  exact eq3