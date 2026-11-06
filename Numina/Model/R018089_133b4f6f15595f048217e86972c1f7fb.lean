import Mathlib

theorem number_theory_700 (a : Fin 10 → ℕ) (ha : a = ![6907, 73, 769, 3043, 19, 1480, 373, 41321, 21768, 178]) :
    ∃ s : Finset (Fin 10), ∑ i ∈ s, a i = 25758 := by
  use {2, 3, 8, 9}
  rw [ha]
  simp [Finset.sum_insert, Finset.sum_singleton]
  <;> try { native_decide }