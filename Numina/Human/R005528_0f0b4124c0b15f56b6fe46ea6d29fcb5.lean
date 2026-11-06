import Mathlib

open Finset

/-
Theorem: Probability of 7 rainbow beads forming the exact rainbow order (red to violet left-to-right) when placed by randomly choosing unused beads and adding to left/right ends.
-/
theorem combinatorics_608671 
    (p : ℕ → ℝ)  
    (p₁ : p 1 = 1) 
    (hp : ∀ n ≥ 2, p n = p (n - 1) / n) :
    p 7 = 1 / 5040 := by
  
  -- Prove by induction that p(n) = 1/n! for all n ≥ 1
  have h1 : ∀ n, n ≥ 1 → p n = 1 / n.factorial := by
    
    -- Fix n with n ≥ 1
    intro n hn 

    -- Mathematical induction on n
    induction n with

    -- n=0 is invalid (n ≥ 1), derive contradiction
    | zero =>  
      exfalso
      linarith

     -- Inductive step: Prove for n+1 using ih for n
    | succ n ih =>
      cases n with

      -- n+1=1: Check base case matches 1/1!
      | zero =>
        norm_num [p₁]

       -- n+1 ≥ 2: Use recursive relation
      | succ n =>

        -- Inductive hypothesis: p(n+1 - 1) = 1/(n+1 - 1)! = 1/n!
        have h2 := ih (by linarith)

        -- Apply hp: p(n+2) = p(n+1)/(n+2)
        have eq1 := hp (n + 2) (by linarith)

        -- Simplify index to n+1
        simp [show n + 2 - 1 = n + 1 by omega] at eq1

        -- Substitute p(n+1) = 1/n! into the equation
        rw [eq1, h2]

        -- Simplify factorial: (n+2)! = (n+2) * (n+1)!
        simp [Nat.factorial]

        -- Reduce fraction: 1/(n+2) * 1/n! = 1/(n+2)!
        field_simp [Nat.factorial]
        ring_nf
  
  -- Apply the general result to n=7
  have h2 := h1 7 (by norm_num)
  have h3 : (7 : ℕ).factorial = 5040 := by decide
  rw [h2, h3] 
  exact rfl