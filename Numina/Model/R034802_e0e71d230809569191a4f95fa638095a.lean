import Mathlib
theorem number_theory_604464 (a : ℕ → ℕ) (hn : ∀ n > 0, a n = (∑ i in Finset.range n, (i + 1)) % 10) : ∑ i in Finset.range 1992, a (i + 1) = 6984:= by 
  rw [Finset.sum_congr rfl (fun i _ => hn (i + 1) (by linarith))]
  native_decide