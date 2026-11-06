import Mathlib

open Finset Real Nat

/-Compute the sum of the three smallest positive integers n for which
(∑ i ∈ Icc 1 (2024 * n), i) / (∑ i ∈ Icc 1 (4 * n), i) is an integer.-/
theorem number_theory_610797: {n: ℕ | n ≤ 63 ∧ 1 ≤ n ∧ ∑ i ∈ Icc 1 (4 * n), i ∣ ∑ i ∈ Icc 1 (2024 * n), i} = {1,25,63} := by
  have sum_eq: ∀ k: ℕ, ∑ i ∈ Icc 1 (2 * k),i = k * (2 * k + 1) := by  -- firstly compute the sum --
    intro k
    induction' k with k hk
    . simp
    . nth_rewrite 1[show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      rw [Finset.sum_Icc_succ_top]
      rw [Finset.sum_Icc_succ_top]
      rw [hk]
      ring
      omega
      omega
  ext n
  constructor
  -- First direction: if n satisfies the equation, then it must be one of our three solutions --
  . intro hn
    simp at hn
    rcases hn with ⟨hn1, hn2, h⟩
    have h1:= sum_eq (2 * n)   -- simplify the left --
    rw [show 2 * (2 * n) = 4 * n by ring] at h1
    rw [h1] at h
    have h2:= sum_eq (1012 * n) -- simplify the right --
    rw [show 2 * (1012 * n) = 2024 * n by ring] at h2
    rw [h2] at h
    clear h1 h2 sum_eq
    simp
    rw [show 1012 * n * (2024 * n + 1) = (2 * n) * (506 * (2024 * n + 1)) by ring] at h
    have g: 0 < 2 * n := by omega
    rw [Nat.mul_dvd_mul_iff_left g] at h
    clear g
    rw [show (506 * (2024 * n + 1)) = 2 * (253 * (2024 * n + 1)) by ring] at h
    replace h: 4 * n + 1 ∣ 253 * (2024 * n + 1) := by
      apply Nat.Coprime.dvd_of_dvd_mul_left at h
      exact h
      simp
      simp [Odd]
      use 2 * n
      omega
    replace h: 4 * n + 1 ∣ 253 * 2020 * n := by
      have id: 253 * 2020 * n = 253 * (2024 * n + 1) - 253 * (4 * n + 1) := by omega
      have o: 4 * n + 1 ∣ 253 * (4 * n + 1) := by apply Nat.dvd_mul_left
      rw [id]
      have ineq: 253 * (4 * n + 1) ≤ 253 * (2024 * n + 1) := by omega
      apply Nat.dvd_sub ineq h o
    rw [show 253 * 2020 * n = (4 * n) * (505 * 253) by ring] at h
    replace h: 4 * n + 1 ∣ 505 * 253 := by
      apply Nat.Coprime.dvd_of_dvd_mul_left at h
      exact h
      rw [Nat.coprime_self_add_left]
      simp
    have hn: n ∈ Icc 1 63 := by simp; omega  -- enumerate the possible values of n --
    fin_cases hn
    all_goals omega

  -- Second direction: if n is one of our three solutions, then it satisfies the equation --
  . intro hn
    simp at hn
    simp
    have h1:= sum_eq (2 * n)   -- simplify the left --
    rw [show 2 * (2 * n) = 4 * n by ring] at h1
    rw [h1]
    have h2:= sum_eq (1012 * n) -- simplify the right --
    rw [show 2 * (1012 * n) = 2024 * n by ring] at h2
    rw [h2]
    clear h1 h2 sum_eq
    rcases hn with h | h | h
    . simp [h]
      norm_num
    . simp [h]
      norm_num
    . simp [h]
      norm_num