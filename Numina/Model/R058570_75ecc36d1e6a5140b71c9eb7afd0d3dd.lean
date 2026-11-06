import Mathlib

theorem number_theory_117151 {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (x : Fin n → ℕ) (y : Fin m → ℕ) (hsum : ∑ i : Fin n, x i = ∑ j : Fin m, y j)
    (hmn : ∑ i : Fin n, x i < m * n) :
    ∃ t : Finset (Fin n), ∃ u : Finset (Fin m),
      (∑ i ∈ t, x i) = (∑ j ∈ u, y j) ∧
      (∑ i ∈ (Finset.univ \ t), x i) = (∑ j ∈ (Finset.univ \ u), y j) := by
  use ∅
  use ∅
  constructor
  · -- Show that ∑ i ∈ (∅ : Finset (Fin n)), x i = ∑ j ∈ (∅ : Finset (Fin m)), y j
    simp
  · -- Show that ∑ i ∈ (Finset.univ \ (∅ : Finset (Fin n))), x i = ∑ j ∈ (Finset.univ \ (∅ : Finset (Fin m))), y j
    simp [hsum]