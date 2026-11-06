import Mathlib

open Real
open scoped BigOperators

theorem number_theory_41086 {n : ℕ} (hn : 0 < n) :
    ∃ k, ∃ a b : Fin k → ℝ,
      (∀ i, 0 < a i ∧ a i < b i) ∧
      (∀ i, ∀ x ∈ Set.Ioo (a i) (b i), ∀ p q : ℤ, q ≤ n^2 → q ≠ 0 → |x - p/q| > 1/n^3) ∧
      (∑ i, (b i - a i)) ≤ 100 / n := by
  use 0
  use fun i => (0 : ℝ), fun i => (0 : ℝ)
  constructor
  · -- Show that ∀ i, 0 < a i ∧ a i < b i
    simp
  constructor
  · -- Show that ∀ i, ∀ x ∈ Set.Ioo (a i) (b i), ∀ p q : ℤ, q ≤ n^2 → q ≠ 0 → |x - p/q| > 1/n^3
    simp
  · -- Show that ∑ i, (b i - a i) ≤ 100 / n
    simp at *
    all_goals
      have h1 : (n : ℝ) ≥ 1 := by exact_mod_cast (show n ≥ 1 by omega)
      have h2 : (100 / (n : ℝ)) ≥ 0 := by
        apply div_nonneg
        all_goals
          norm_num
        all_goals
          try { linarith [h1] }
          all_goals try { nlinarith [h1] }
      linarith [h2]