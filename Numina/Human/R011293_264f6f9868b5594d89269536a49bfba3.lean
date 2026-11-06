import Mathlib

open Nat

/-Let $N$ be the smallest positive integer such that in any sequence of $N$ consecutive positive integers, at least one integer is coprime to $374$. Given that $374 = 2 \times 11 \times 17$, what is the smallest possible value of $N$?-/
theorem number_theory_616097 : IsLeast {N : ℕ | 0 < N ∧ ∀ k, ∃ m ∈ Finset.Icc k (k + N - 1), Nat.Coprime m 374} 6 := by
  constructor
  · simp only [Finset.mem_Icc, Set.mem_setOf_eq, ofNat_pos, Nat.add_one_sub_one, true_and]
    intro n
    have : ∀n, ¬n.Coprime 374 → 2 ∣ n ∨ 11 ∣ n ∨ 17 ∣ n := by
      have : ∀n < 374, ¬n.gcd 374 = 1 → 2 ∣ n ∨ 11 ∣ n ∨ 17 ∣ n := by native_decide
      simp only [ne_eq]
      intro n hn
      rw [Nat.gcd_comm, Nat.gcd_rec] at hn
      specialize this (n % 374) (by omega) hn
      omega
    by_cases hn₁ : Even n
    · -- if n is even, n + 1, n + 3, n + 5 are odd, and one of them is coprime to 374
      by_cases hn₂ : (n + 1).Coprime 374
      · use n + 1
        omega
      by_cases hn₃ : (n + 3).Coprime 374
      · use n + 3
        omega
      by_cases hn₄ : (n + 5).Coprime 374
      · use n + 5
        omega
      -- Now, if n+1, n+3, n+5 are not coprime to 374, it will conclude a contradiction.
      have h₁ := this (n + 1) hn₂
      have h₂ := this (n + 3) hn₃
      have h₃ := this (n + 5) hn₄
      have h₄ : ¬2 ∣ n + 1 := by
        simp only [two_dvd_ne_zero]
        apply odd_iff.mp
        exact Even.add_one hn₁
      simp only [Nat.dvd_add_self_right, h₄, false_or] at h₁ h₂ h₃
      omega
    -- if n is odd, n + 2, n + 4 are odd too.
    by_cases hn₂ : n.Coprime 374
    · use n
      omega
    by_cases hn₃ : (n + 2).Coprime 374
    · use n + 2
      omega
    by_cases hn₄ : (n + 4).Coprime 374
    · use n + 4
      omega
    -- Now, if n, n+2, n+4 are not coprime to 374, it will conclude a contradiction.
    have h₁ := this n hn₂
    have h₂ := this (n + 2) hn₃
    have h₃ := this (n + 4) hn₄
    rw [Nat.not_even_iff_odd] at hn₁
    have h₄ : ¬2 ∣ n := by
      simp only [two_dvd_ne_zero]
      apply odd_iff.mp
      exact hn₁
    simp only [Nat.dvd_add_self_right, h₄, false_or] at h₁ h₂ h₃
    omega
  · intro n hn
    by_contra!
    suffices ∀ p ∈ Set.Icc 0 5, ¬ p ∈ {N | 0 < N ∧ ∀ (k : ℕ), ∃ m ∈ Finset.Icc k (k + N - 1), m.Coprime 374} by apply this n (by simp [show n ≤ 5 by omega]) hn
    intro p
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq]
    intro hp
    interval_cases p
    · -- p = 0
      simp
    · -- p = 1
      simp only [zero_lt_one, add_tsub_cancel_right, Finset.Icc_self, Finset.mem_singleton,
        exists_eq_left, true_and, not_forall, ne_eq]
      use 2
      simp
    all_goals
    · -- 3 ≤ p ≤ 5
      simp only [ofNat_pos, Nat.add_one_sub_one, Finset.mem_Icc, true_and, not_forall, not_exists, not_and, ne_eq, and_imp]
      use 252
      native_decide
