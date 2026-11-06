import Mathlib

theorem number_theory_155760 (n : ℕ) (h : n > 0) :
    (n^3 + (n+1)^3 + (n+2)^3 = (n+3)^3 ↔ n = 3) ∧
    ¬∃ m, m > 0 ∧ m^3 + (m+1)^3 + (m+2)^3 + (m+3)^3 = (m+4)^3 := by
  constructor
  · -- Show that n^3 + (n+1)^3 + (n+2)^3 = (n+3)^3 if and only if n = 3
    constructor
    · -- Prove the forward direction: if the equation holds, then n = 3
      intro h_eq
      have h1 : n ≤ 9 := by
        nlinarith [sq_nonneg ((n : ℤ) - 3), sq_nonneg ((n + 1 : ℤ) - 3), sq_nonneg ((n + 2 : ℤ) - 3), sq_nonneg ((n + 3 : ℤ) - 3), sq_nonneg ((n : ℤ) - 3), sq_nonneg ((n + 1 : ℤ) - 3), sq_nonneg ((n + 2 : ℤ) - 3), sq_nonneg ((n + 3 : ℤ) - 3)]
      interval_cases n <;> omega
    · -- Prove the reverse direction: if n = 3, then the equation holds
      intro h_eq
      rw [h_eq]
      all_goals norm_num
  · -- Show that there's no solution for the second part
    intro h
    rcases h with ⟨m, hm1, hm2⟩
    have h1 : m ≤ 3 := by
      nlinarith [sq_nonneg (m ^ 2 : ℕ), sq_nonneg ((m : ℤ) - 2), sq_nonneg ((m + 4 : ℤ)), sq_nonneg ((m - 1) : ℤ), sq_nonneg ((m -3) : ℤ), sq_nonneg ((m + 1) : ℤ), sq_nonneg ((m + 2) : ℤ)]
    interval_cases m <;> omega