import Mathlib

open Finset Real

theorem inequalities_201033 {n : ℕ} (hn : 0 < n) (a : Fin 2 → Fin n → ℝ)
    (ha : ∀ i j, 0 < a i j) (h : ∀ j, a 0 j + a 1 j = 1) :
    ∃ b : Fin 2 → Fin n → ℝ,
      (∀ i j, b i j = a i j ∨ b i j = 0) ∧
      (∀ i, ∑ j : Fin n, b i j ≤ (n + 1) / 4) := by
  use fun i j => 0
  constructor
  · -- Show that in each entry, `b i j` is either the original value or 0
    intro i j
    simp
    <;> try linarith
  · -- Show that the sum in each row is at most (n + 1) / 4
    intro i
    simp
    all_goals
      have hn' : (n : ℝ) > 0 := by exact_mod_cast hn
      positivity