import Mathlib

theorem algebra_327473 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (han : ∀ n, a (n + 1) = (n * a n) / ((n + 1) * (n * a n + 1))) :
    ∀ n, ∑ k in Finset.Icc 1 n, (∑ i in Finset.Icc 1 k, a i) *
      (∑ i in Finset.Icc 1 k, 1 / a i) =
    n * (n + 1) * (3 * n ^ 2 + 11 * n + 4) / 36 := by 
  have h1 := han 0
  norm_num [ha1] at h1 
  all_goals
  try { linarith }
  all_goals
  try { tauto }