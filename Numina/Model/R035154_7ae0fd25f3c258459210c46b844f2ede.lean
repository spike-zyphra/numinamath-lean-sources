import Mathlib

theorem algebra_132573 {a : ℕ → ℝ} (ha : ∀ n, n ∈ Finset.Icc 1 6 → a n = n)
    (ha' : ∀ n, n ≥ 7 → a n = -a (n - 3)) : a 2023 = -4 := by

  set_option maxRecDepth 10000 in
  norm_num [ha, ha', Finset.mem_Icc] at *
  all_goals try { linarith }