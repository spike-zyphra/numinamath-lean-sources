import Mathlib

open Finset

theorem algebra_288559 {a : ℕ → ℝ → ℝ}
    -- Initial condition: a_0(x) = 1 for all x
    (ha0 : ∀ x, a 0 x = 1)
    -- Initial condition: a_1(x) = x^2 + x + 1 for all x
    (ha1 : ∀ x, a 1 x = x ^ 2 + x + 1)
    -- Recursive definition: a_n(x) = (x^n + 1) * a_{n-1}(x) - a_{n-2}(x) for n ≥ 2
    (han : ∀ n ≥ 2, ∀ x, a n x = (x ^ n + 1) * a (n - 1) x - a (n - 2) x) :
    a 2010 1 = 4021 := by
  have h1 : ∀ (n : ℕ), a n 1 = (2 * ((n : ℝ) ) + 1) := by
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with
    | zero =>
      rw [ha0 1]
      norm_num 
    | succ n =>
      cases n with 
      | zero => 
        rw [ha1 1]
        norm_num 
      | succ n => 
        have h2 := ih (n + 1) (by linarith) 
        have h3 := ih (n) (by linarith) 
        have h4 : a (n + 2) 1 = ( (1 : ℝ) ^ (n + 2 : ℕ) + 1 ) * a (n + 1) 1 - a (n ) 1 := by
          specialize han (n + 2) (by linarith) 1
          simpa using han 
        rw [h4]
        rw [h2, h3]
        field_simp
        ring_nf 
  have h2 := h1 2010
  norm_num at h2 ⊢
  linarith