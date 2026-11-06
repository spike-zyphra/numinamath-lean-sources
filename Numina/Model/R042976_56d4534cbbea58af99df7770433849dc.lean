import Mathlib

open Nat

def is_composite (n : ℕ) := n ≠ 1 ∧ ¬n.Prime

theorem number_theory_173919 (n : ℕ) :
    ∃ k, ∀ i ∈ Finset.range n, is_composite (k + i) := by
  use (n + 1).factorial + 2
  intro i hi
  have h1 : i < n := by
    simp at hi ⊢
    omega
  have h2 : ((n + 1).factorial + 2 + i) ≠ 1 := by
    have h3 : (n + 1).factorial ≥ 1 := by
      apply Nat.factorial_pos
    have h4 : (n + 1).factorial + 2 + i ≥ 3 := by
      omega
    omega
  have h3 : ¬ ((n + 1).factorial + 2 + i).Prime := by
    have h4 : i + 2 ≤ n + 1 := by 
      omega 
    -- Show that `i + 2` divides `(n + 1).factorial`
    have h5 : (i + 2) ∣ (n + 1).factorial := by 
      apply Nat.dvd_factorial
      all_goals 
        omega
    -- Show that `i + 2` divides `(n + 1).factorial + 2 + i`
    have h6 : (i + 2) ∣ ((n + 1).factorial + 2 + i) := by
      have h7 : (i + 2) ∣ (n + 1).factorial := h5 
      have h8 : (i + 2) ∣ (i + 2) := by 
        simp 
      have h9 : (i + 2) ∣ ((n + 1).factorial + (i + 2)) := by
        apply Nat.dvd_add 
        all_goals 
          try assumption 
          all_goals 
            try { 
              tauto 
            }
            all_goals 
              try { 
                nlinarith 
              }
      have h10 : (n + 1).factorial + 2 + i = (n + 1).factorial + (i + 2) := by
        omega 
      rw [h10] 
      exact h9 
    -- Show that the number is greater than 1
    have h7 : (n + 1).factorial + 2 + i > 1 := by 
      have h3 : (n + 1).factorial ≥ 1 := by
        apply Nat.factorial_pos 
      omega 
    -- Show that the divisor is greater than 1
    have h8 : i + 2 > 1 := by 
      omega 
    -- Show that the quotient is also greater than 1
    -- The number `(n + 1).factorial + 2 + i` is divisible by `i + 2`, which is greater than 1, and the quotient is also greater than 1. Thus, it's composite.
    -- We can show this happens by using existence of a proper divisibility.
    have h9 : ((n + 1).factorial + 2 + i) > (i + 2) := by 
      have h10 : (n + 1).factorial ≥ 1 := by
        apply Nat.factorial_pos 
      omega 
    -- Now use the divisibility to show non-primality
    apply Nat.not_prime_of_dvd_of_lt (show (i + 2) ∣ ((n + 1).factorial + 2 + i) by assumption)
    all_goals 
      omega 
  exact ⟨h2, h3⟩