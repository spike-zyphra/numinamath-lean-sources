import Mathlib

open Finset Real

theorem algebra_186131 {k : ℕ} (x : ℝ) :
    ∏ i ∈ range k, (1 + x^(2^i)) = ∑ i ∈ range (2^k), x^i := by
  have h1 : ∀ k : ℕ, ∏ i ∈ range k, (1 + x ^ (2 ^ i)) = ∑ i in range (2 ^ k), x ^ i := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [prod_range_succ, ih]
      have eq3 : ∑ i in range (2 ^ (k + 1)), x ^ i =
          (∑ i in range (2 ^ k), x ^ i) + ∑ i in range (2 ^ k), x ^ (2 ^ k + i) := by
        have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
          ring_nf
        rw [h2]
        rw [Finset.sum_range_add]
        all_goals try { simp_all [Finset.sum_range_succ] }
      rw [eq3]
      have eq4 : ∑ i in range (2 ^ k), x ^ (2 ^ k + i) = (∑ i in range (2 ^ k), x ^ i) * x ^ (2 ^ k) := by
        have h3 : ∀ m : ℕ, ∑ i in range m, x ^ (2 ^ k + i) = (∑ i in range m, x ^ i) * x ^ (2 ^ k) := by
          intro m
          induction m with
          | zero =>
            simp
          | succ m ih =>
            rw [sum_range_succ, sum_range_succ, ih]
            all_goals ring
        exact h3 (2 ^ k)
      rw [eq4]
      ring
  specialize h1 k
  simpa using h1