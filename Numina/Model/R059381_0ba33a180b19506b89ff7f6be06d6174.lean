import Mathlib

theorem number_theory_31551 {n : ℕ} (hn : 4 ≤ n) (a : Finset ℕ)
    (ha : ∀ x ∈ a, 0 < x ∧ x < 2 * n) (hdist : a.card = n) :
    ∃ t ⊆ a, ∑ x ∈ t, x ≡ 0 [ZMOD 2 * n] := by
  use ∅
  simp
  <;> try norm_num [Int.ModEq, Finset.sum_eq_zero]
  all_goals omega