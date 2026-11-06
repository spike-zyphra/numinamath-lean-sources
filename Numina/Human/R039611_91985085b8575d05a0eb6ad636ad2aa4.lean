import Mathlib

open Nat

/-Find the sum of all positive integers $n$ such that $n$ divides $n^{2}+n+2$.-/

theorem number_theory_608427 {n : ℕ} (h : n ∣ (n^2 + n + 2)) : n = 1 ∨ n = 2 := by
  have h1 : n ∣ (n^2 + n) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h]

  --easy to find that n | 2
  have h2 : n ∣ 2 := by 
    have : n ∣ (n ^ 2 + n + 2) - (n ^ 2 + n) := by 
      apply Nat.dvd_sub
      simp
      exact h
      exact h1
    simp at this
    exact this

  -- then we can try n = 1 and 2 which satisfy the condition.
  have h3 : n ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  interval_cases n <;> simp_all