import Mathlib

theorem number_theory_310537 (a : ℕ → ℕ) (ha : ∀ n, a n = (n ^ 4) % 10) :
    ∑ i in Finset.range 2008, a (i + 1) = 6632 := by
  rw [Finset.sum_congr rfl (fun i _ => ha (i + 1))]
  native_decide