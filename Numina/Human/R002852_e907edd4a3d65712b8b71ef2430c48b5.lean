import Mathlib

theorem number_theory_122116 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℤ) :
    ∑ i : Fin n, a i * b i = ∑ i : Fin n, b i * a i := by
  apply Finset.sum_congr rfl
  intros i hi
  ring