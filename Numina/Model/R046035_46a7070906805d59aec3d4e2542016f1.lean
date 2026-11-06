import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic

open Nat

theorem algebra_241253 (n : ℤ) (p : ℕ) (hn : n ≠ 0) (hp : Nat.Prime p)
    (h : 6 * n ^ 2 - (2 * p + 9) * n + p + 3 = 0) :
    n = 2 ∧ p = 3 := by
  have eq1 : (3 * n - (p + 3 : ℤ)) * (2 * n - 1) = 0 := by
    ring_nf at h ⊢
    nlinarith
  cases' (mul_eq_zero.1 eq1) with h1 h2
  · -- Case where `3n - (p + 3) = 0`
    have eq2 : 3 * n = (p + 3 : ℤ) := by 
      linarith
    have eq3 : (p : ℤ) = 3 * (n - 1) := by
      nlinarith
    have hp2 : p = 3 := by
      have h9 : p % 3 = 0 := by
        omega
      by_cases h10 : p > 3
      · -- `p` is a prime greater 3 and divisible 3
        have h11 : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals omega
        contradiction
      · -- p ≤ 3
        interval_cases p <;> try tauto
    have eq4 : n = 2 := by
      have eq3 : (p : ℤ) = 3 * (n - 1) := eq3
      rw [show (p : ℤ) = 3 by exact_mod_cast hp2] at eq3
      omega
    exact ⟨eq4, hp2⟩
  · -- Case where `2n - 1 = 0`
    have h8 : 2 * n = 1 := by
      linarith
    omega