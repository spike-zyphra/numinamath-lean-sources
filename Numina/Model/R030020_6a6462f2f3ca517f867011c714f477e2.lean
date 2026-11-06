import Mathlib

theorem algebra_145553 (S : ℕ → ℤ) (hS : ∀ n, S n = -2 * n ^ 3 + 21 * n ^ 2 + 23 * n) :
    IsGreatest {x | ∃ n, S n = x} 504 := by
  constructor
  · use 7
    rw [hS]
    all_goals norm_num 
  · -- Show that 504 is greatest
    intro x hx
    rcases hx with ⟨n, hn⟩
    rw [hS] at hn
    by_contra h
    push_neg at h
    have h2 : -2 * (n : ℤ) ^ 3 + 21 * (n : ℤ) ^ 2 + 23 * (n : ℤ) ≤ 504 := by
      by_contra h
      push_neg at h
      have h3 : n > 8 := by
        by_contra h
        push_neg at h
        interval_cases n <;> try { omega }
      have h4 : n ≥ 9 := by omega
      nlinarith [sq_nonneg ((n : ℤ) - 7), sq_nonneg ((n : ℤ) - 8), sq_nonneg ((n : ℤ) ^ 2 - 15 * (n : ℤ)), sq_nonneg ((n : ℤ) * (n : ℤ) - 0), sq_nonneg ((n : ℤ) * (n : ℤ) * (n : ℤ) * (n : ℤ)), sq_nonneg ((n : ℤ) - 8), sq_nonneg ((n : ℤ) - 8), sq_nonneg ((n : ℤ) * (n : ℤ) - 7 * n), sq_nonneg ((n : ℤ) * (n : ℤ) - 7 * n)]
    linarith