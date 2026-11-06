import Mathlib

open Finset Real Nat

/-Let $N$ be a positive integer.
Determine the units digit of the sum $S_N = \sum_{k=1}^{N} k!$.
Show that this units digit is equal to $\left(\sum_{k=1}^{\min(N,4)} k!\right) \pmod{10}$.-/

theorem number_theory_640853 (N S_N: ℕ) (h1: 0 < N) (h2: S_N = ∑ k ∈ Icc 1 N, Nat.factorial k):
  S_N % 10 = (∑ k ∈ Icc 1 (min N 4), Nat.factorial k) % 10 := by

  by_cases l: N ≤ 4
  .
    rw [show min N 4 = N by simp; omega]
    rw [← h2]
  .
    -- case when 4 < N
    simp at l
    rw [show min N 4 = 4 by omega]
    set A:= ∑ k ∈ Icc 1 4, Nat.factorial k
    set B:= ∑ k ∈ Icc 5 N, Nat.factorial k

    -- we split the sum into two parts
    have eq: S_N = A + B := by
      simp only [h2, A, B]
      clear *- l
      have f1: Icc 1 N = Icc 1 4 ∪ Icc 5 N := by
        ext k
        simp
        omega
      have f2: Disjoint (Icc 1 4) (Icc 5 N) := by
        intro s h1 h2
        simp at *
        ext k
        simp
        by_contra! g
        have g1: k ∈ Icc 1 4 := by
          exact Set.mem_of_mem_of_subset g h1
        have g2: k ∈ Icc 5 N := by
          exact Set.mem_of_mem_of_subset g h2
        simp at g1 g2
        omega

      rw [f1, Finset.sum_union f2]
    rw [eq]
    rw [Nat.add_mod]
    suffices B % 10 = 0 by
      rw [this]
      simp
    simp only [B]
    rw [Finset.sum_nat_mod]
    suffices (∑ i ∈ Icc 5 N, i ! % 10) = 0 by
      rw [this]
    clear *- l

    -- then we prove the mod equation by induction on N
    induction' N with n ih
    .
      simp at l
    .
      by_cases h: n = 4
      .
        simp [h]
        native_decide
      .
        replace l: 4 < n := by
          omega
        have l':= l
        apply ih at l
        rw [Finset.sum_Icc_succ_top, l]
        .
          simp
          apply Nat.mod_eq_zero_of_dvd
          suffices 2 ∣ Nat.factorial (n + 1) ∧ 5 ∣ Nat.factorial (n + 1) by
            omega
          constructor
          .
            apply Nat.dvd_factorial
            norm_num
            omega
          .
            apply Nat.dvd_factorial
            norm_num
            omega
        .
          omega
