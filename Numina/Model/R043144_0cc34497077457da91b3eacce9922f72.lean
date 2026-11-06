import Mathlib

open Real
open scoped BigOperators

theorem inequalities_602037 {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
  (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
  ∑ i, a i ^ k > 0 := by

  have h1 : ∀ i : Fin n, a i ^ k > 0 := by
    intro i
    have ha_pos : 0 < a i := ha i
    have h2 : a i ^ k > 0 := by
      apply pow_pos
      exact ha_pos
    exact h2

  have h2 : ∑ i : Fin n, a i ^ k > 0 := by
    apply Finset.sum_pos
    · -- Show each term is positive
      intro i hi
      specialize h1 i
      simpa using h1
    · -- Show the indexing set is non-empty
      use ⟨0, by omega⟩
      all_goals simp [ha]

  exact h2