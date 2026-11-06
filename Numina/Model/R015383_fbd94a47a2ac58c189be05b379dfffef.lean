import Mathlib

theorem number_theory_132736 {n : ℕ} (hn : n > 0) (h : ∑ i ∈ Finset.Icc 1 (2 * n), i = 963 + ∑ i ∈ Finset.Icc 1 2, i) :
    n = 44 ∧ (2 * n - 1) = 89 ∧ (2 * n) = 90 := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 (2 * n), i = n * (2 * n + 1) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by ring]
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      ring
  have h2 : ∑ i ∈ Finset.Icc 1 (2 * n), i = n * (2 * n + 1) := by 
    apply h1
  have h3 : ∑ i ∈ Finset.Icc 1 2, i = 3 := by
    norm_num [Finset.sum_Icc_succ_top]
  rw [h2, h3] at h
  have h4 : n ≤ 32 := by
    nlinarith
  interval_cases n <;> omega