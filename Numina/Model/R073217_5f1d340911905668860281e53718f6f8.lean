import Mathlib

open BigOperators

theorem algebra_605499 {P Q : Polynomial ℤ} (a : ℕ → ℤ)
(ha : ∀ n, a n = Nat.factorial n + n) (h : ∀ n, ∃ m : ℤ, P.eval (a n) / Q.eval (a n) = m): ∀ n, Q.eval n ≠ 0 → ∃ m : ℤ, P.eval n / Q.eval n = m := by 
  intro n hn
  refine' ⟨P.eval n / Q.eval n, by omega⟩