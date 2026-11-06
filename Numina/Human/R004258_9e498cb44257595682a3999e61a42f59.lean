import Mathlib

open Finset Real

/-
Problem:
For each positive integer n, find the number of n-digit positive integers for which:
1 No two consecutive digits are equal
2.The last digit is a prime number (2, 3, 5, 7)
-/
theorem combinatorics_245998 
    (n : ℕ) 
    (a : ℕ → ℝ)
    (ha₀ : a 0 = 0) 
    (ha₁ : a 1 = 4)
    (ha : ∀ n, a (n + 1) + a n = 4 * 9 ^ n) :
    a n = (2 / 5) * (9 ^ n - (- 1) ^ n) := by

  -- Define the inductive hypothesis for strong induction
  have h2 : ∀ (n : ℕ), a n = (2 / 5) * (9 ^ n - (- 1) ^ n) := by 
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>

      -- Base case: n = 0, by definition a₀ = 0
      have h : a 0 = 0 := ha₀
      simp [h] 
    | succ n =>

      -- Split into cases for n = 1 and n > 1
      cases n with 
      | zero =>

        -- Base case: n = 1, by definition a₁ = 4
        rw [ha₁]
        norm_num 
      | succ n =>

        -- Inductive step: assume the formula holds for all k < n+2
        have h1 := ih (n + 1) (by linarith)
        have h2 := ih (n) (by linarith)

        -- Apply the recurrence relation a(n+1) + a(n) = 4·9ⁿ
        have eq1 := ha (n + 1)
        simp [show n + 1 + 1 = n + 2 by omega] at eq1 
        simp [show n + 1 = n + 1 by rfl] at h1 h2 

        -- Rewrite the recurrence relation for clarity
        have eq3 : a (n + 2) + a (n + 1) = 4 * (9:ℝ) ^ (n + 1) := by 
          linarith [eq1]

        -- Substitute a(n+1) using the inductive hypothesis
        have eq4 : a (n + 1) = (2 / 5) * (9 ^ (n + 1) - (-1) ^ (n + 1)) := by 
          linarith [h1]

        -- Solve for a(n+2) using the recurrence relation
        have eq5 : a (n + 2) = 4 * (9:ℝ) ^ (n + 1) - a (n + 1) := by 
          linarith 

        -- Substitute and simplify using field arithmetic and ring normalization
        rw [eq5, eq4]
        field_simp at *
        ring_nf 

  -- Specialize the general result to the specific n and simplify
  specialize h2 n 
  simpa using h2  