import Mathlib

open Finset BigOperators

theorem algebra_2685 {n : ℕ} {a : ℕ → ℤ} (h : ∀ j ∈ Icc 1 n, a j ≥ 1)
  (h' : ∀ i ∈ Icc 1 n, ∀ j ∈ Icc 1 n, a i = a j → i = j) (k : ℕ) (hk : 0 < k) : ∃ j : ℤ, ∑ i ∈ Icc 1 n, (a i) ^ (n + 1) / ∏ j ∈ (Icc 1 n).erase i, ((a i : ℤ) - (a j : ℤ)) = j := by 
  refine ⟨∑ i ∈ Icc 1 n, (a i) ^ (n + 1) / ∏ j ∈ (Icc 1 n).erase i, ((a i : ℤ) - (a j : ℤ)), by simp⟩