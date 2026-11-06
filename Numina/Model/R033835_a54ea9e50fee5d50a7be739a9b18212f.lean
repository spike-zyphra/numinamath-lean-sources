import Mathlib

theorem number_theory_303385 {n : ℕ} (hn : ∃ k, 9 * n ^ 2 + 5 * n + 26 = k * (k + 1)) :
    n = 6 ∨ n = 2 := by 
  rcases hn with ⟨k, hk⟩ 
  have hk_eq : k ^ 2 + k = 9 * n ^ 2 + 5 * n + 26 := by
    nlinarith
  have h6 : k ≤ 3 * n + 4 := by
    nlinarith [sq_nonneg ((k : ℕ) - (3 * n + 5) : ℤ), sq_nonneg ((k + 1 : ℕ) - (3 * n + 6) : ℤ)]
  have h1 : k ≥ 3 * n + 1 := by
    nlinarith [sq_nonneg ((k : ℕ) - (3 * n) : ℤ), sq_nonneg ((k + 1 : ℕ) - (3 * n + 1) : ℤ)]
  have h8 : k = 3 * n + 1 ∨ k = 3 * n + 2 ∨ k = 3 * n + 3 ∨ k = 3 * n + 4 := by 
    omega
  rcases h8 with (h8 | h8 | h8 | h8)
  · -- k=3n+1
    rw [show k = 3 * n + 1 by omega] at hk_eq
    ring_nf at hk_eq 
    have hn6 : n = 6 := by
      nlinarith 
    left 
    exact hn6
  · -- k=3n+2
    rw [show k = 3 * n + 2 by omega] at hk_eq
    ring_nf at hk_eq 
    have hn2 : n = 2 := by
      nlinarith 
    right 
    exact hn2
  · -- k=3n+3
    rw [show k = 3 * n + 3 by omega] at hk_eq
    ring_nf at hk_eq 
    exfalso 
    omega 
  · -- k=3n+4
    rw [show k = 3 * n + 4 by omega] at hk_eq
    ring_nf at hk_eq 
    exfalso 
    omega