import Mathlib

open Finset

theorem number_theory_223656 {a : ℕ → ℕ} (ha : ∀ n, a n = if Even n then 0 else 1) :
    (∑ i ∈ range 10, a i * 10 ^ i) % 2 = 0 := by
  norm_num [sum_range_succ, ha, Nat.even_iff]
  <;> try native_decide
  <;> try { native_decide }
  <;> try { aesop }
  <;> try { native_decide }
  <;> try native_decide