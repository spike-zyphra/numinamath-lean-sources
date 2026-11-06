import Mathlib

theorem number_theory_255760 {n m : ℕ} (hn : n = 111111 * 1111111111) :
    (Nat.digits 10 n).length = 15 := by
  rw [hn]
  norm_num