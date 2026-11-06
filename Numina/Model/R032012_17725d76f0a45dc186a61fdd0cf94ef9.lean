import Mathlib

open Finset

theorem algebra_96068 {S T s t : ℕ → ℝ} {p q : ℝ} (hs : ∀ n, s (n + 1) = s n + p)
    (hr : ∀ n, t (n + 1) = t n + q) (hS : ∀ n, S n = ∑ i ∈ Icc 1 n, s i)
    (hT : ∀ n, T n = ∑ i ∈ Icc 1 n, t i) (hST : ∀ n, S n / T n = (7 * n + 1) / (4 * n + 27)) :
    s 11 / t 11 = 4 / 3 := by
  have h0 := hST 0
  norm_num [hS, hT, sum_eq_zero] at h0
  all_goals linarith