import Mathlib

open Finset

theorem algebra_219916 {a : ℕ → ℕ} (ha1 : a 1 = 4)
    (han : ∀ n, a (n + 1) = ∑ i ∈ range n, Nat.factorial (a i) + 2 * (n + 1) + 1) :
    a 2003 = 11 * 2 ^ 2001 - 2 := by 
  have h0 := han 0
  norm_num [Finset.sum_range_zero] at h0
  rw [ha1] at h0
  all_goals omega