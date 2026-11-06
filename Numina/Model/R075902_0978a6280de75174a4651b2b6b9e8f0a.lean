import Mathlib

theorem number_theory_106045 :
    ∃ f : ℕ → ℕ,
      (∀ n, ∃ m, f n = m ^ 2) ∧
      (∀ n, n ≥ 2 → f n = f (n - 2) + f (n - 1)) := by 
  use fun n => 0
  constructor
  · -- Show that all terms are perfect squares
    intro n
    use 0
    all_goals simp
  · -- Show that each term starting from the third is the sum of the previous two
    intro n hn
    simp