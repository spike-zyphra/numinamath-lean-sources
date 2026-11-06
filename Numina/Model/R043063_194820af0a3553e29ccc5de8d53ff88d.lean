import Mathlib

open Nat

theorem number_theory_2182 : IsGreatest {n | 2^n > n !} 3 := by 
  constructor 
  · -- Show $3 \in \{n \mid 2^n > n!\}$
    native_decide 
  · -- Show that for any $n \in \{n \mid 2^n > n!\}$, $n \leq 3$
    intro n hn
    have h : 2^n > n ! := by
      simpa using hn
    by_contra h'
    push_neg at h'
    have h4 : n ≥ 4 := by
      omega
    have h5 : ∀ (k : ℕ), k ≥ 4 → 2 ^ k ≤ k ! := by 
      intro k hk 
      have base4 : 2 ^ 4 ≤ 4 ! := by 
        norm_num [Nat.factorial]
      have step : ∀ (m : ℕ), m ≥ 4 → 2 ^ m ≤ m ! → 2 ^ (m + 1) ≤ (m + 1) ! := by
        intro m hm h
        have h1 : 2 ^ (m + 1) = 2 ^ m * 2 := by ring 
        have h2 : (m + 1) ! = (m + 1) * m ! := by 
          simp [Nat.factorial]
        rw [h1, h2]
        nlinarith [h, mul_pos (show (0 : ℕ) < 2 by norm_num) (show (0 : ℕ) < 2 by norm_num), 
          Nat.factorial_pos m, Nat.factorial_pos (m + 1), 
          show (m + 1) ≥ 2 by nlinarith
        ]
      exact Nat.le_induction base4 step k hk 
    have h6 : 2 ^ n ≤ n ! := h5 n h4
    linarith