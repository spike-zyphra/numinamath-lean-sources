import Mathlib

theorem number_theory_226912 (α : ℝ) (hα : α > 0) (C : ℝ) (hC : C > 1) :
    ∃ x : ℕ, ∃ y : ℤ, x < C ∧ |(x * α) - y| ≤ 1 / C := by
  use 0
  use 0
  constructor
  · -- Show that (0 : ℝ) < (C : ℝ)
    norm_num at hC ⊢
    all_goals linarith
  · -- Show that |((0 : ℝ) * α) - (0 : ℤ)| ≤ 1 / C
    norm_num
    all_goals positivity