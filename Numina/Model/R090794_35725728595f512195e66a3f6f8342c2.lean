import Mathlib

theorem number_theory_593 {n m : ℕ} (hn : n = ∑ i ∈ Finset.range 1989, 10^i)
    (hm : m = ∑ i ∈ Finset.range 1989, 10^i) :
    (Nat.digits 10 (n * m)).sum = 17901 := by
  rw [hn, hm]
  native_decide