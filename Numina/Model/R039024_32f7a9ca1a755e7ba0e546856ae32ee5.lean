import Mathlib

open Finset

theorem algebra_265899 (n : ℕ) :
    ∏ i ∈ range (n + 1), (1 + 2^(2^i)) = 2^(2^(n + 1)) - 1 := by
  have h1 : ∀ (n : ℕ), ∏ i ∈ range (n + 1), (1 + 2^(2^i)) = 2^(2^(n + 1)) - 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [prod_range_succ]
      rw [ih]
      have eq1 : (2^(2^(n + 1)) - 1 : ℕ) * (1 + 2^(2^(n + 1)) ) = (2^(2^(n + 1)) ) ^ 2 - 1 := by
        cases (2^(2^(n + 1)) ) with
        | zero =>
          simp
        | succ m =>
          simp [Nat.mul_add, Nat.add_mul, mul_add, mul_sub]
          <;> ring_nf <;> omega
      rw [eq1]
      have eq2 : (2^(2^(n + 1)) ) ^ 2 = 2^(2^(n + 1 + 1)) := by
        ring_nf
      rw [eq2]
      all_goals norm_num
      all_goals omega
  specialize h1 n
  simpa using h1