import Mathlib

open Finset

theorem number_theory_36908 : IsGreatest {n : ℕ | 3 ^ n ∣ ∏ i ∈ Icc 2 100, (i ^ 2 - (i - 1) ^ 2)} 49 := by
  constructor
  · -- Show 49 is in the set
    native_decide
  · -- Show no larger element is in the set
    intro n hn
    have h : 3 ^ n ∣ ∏ i ∈ Icc 2 100, (i ^ 2 - (i - 1) ^ 2) := hn
    have h' : n ≤ 49 := by
      by_contra h'
      push_neg at h'
      have h1 : n ≥ 50 := by omega
      -- Now we need to show that 3^50 does not divide the product.
      have h2 : ¬ (3 ^ 50 ∣ ∏ i ∈ Icc 2 100, (i ^ 2 - (i - 1) ^ 2)) := by
        native_decide
      -- Note that 3^n is divisible by 3^50
      have h3 : 3 ^ 50 ∣ 3 ^ n := by
        apply pow_dvd_pow _ (by linarith)
      -- Then 3^50 divides the product by transitivity, which gives a contradiction
      have h4 : 3 ^ 50 ∣ ∏ i ∈ Icc 2 100, (i ^ 2 - (i - 1) ^ 2) := by
        exact dvd_trans h3 h
      contradiction
    linarith