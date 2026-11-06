import Mathlib

theorem inequalities_88266 {n : ℕ} (hn : n > 2) (N : ℕ) (hN : N ≥ 2 * n - 2)
    (a : Fin N → ℤ) (ha : ∀ i, |a i| ≤ n) (hsum : ∑ i, a i < n - 1) :
    ∃ t : Finset (Fin N), ∑ i ∈ t, a i = 0 := by
  use ∅
  simp