import Mathlib

theorem number_theory_263971 (n : ℕ) (hn : n = 1234) :
    (Finset.sum (Finset.range n) fun i => (i + 1) ^ (i + 1)) % 10 = 7 := by 
  rw [hn]
  native_decide