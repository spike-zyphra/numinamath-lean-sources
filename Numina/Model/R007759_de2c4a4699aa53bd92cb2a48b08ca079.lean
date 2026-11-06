import Mathlib

theorem number_theory_285108 (n : ℕ) (h : n = 12) :
    n * (1 - (1 / 2 : ℚ) * (2 / 3 : ℚ)) = 8 := by
  rw [h]
  norm_num
  <;> try { omega }