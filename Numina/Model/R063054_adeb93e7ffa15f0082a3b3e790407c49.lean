import Mathlib

theorem number_theory_188939 {n : ℕ} (hn : n = 10989) :
    (n * 9).digits 10 = List.reverse (n.digits 10) := by 
  rw [hn]
  norm_num