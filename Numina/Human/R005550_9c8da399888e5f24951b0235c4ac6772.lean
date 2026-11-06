import Mathlib

open Real

/-
Problem:
Given a recurrence relation for the probability that Sherry is at a specific vertex after n minutes, find the probability that she is at the vertex opposite her starting position after k minutes.
-/
theorem combinatorics_608780 
    (p : ℕ → ℝ) 
    (hp1 : p 1 = 1) 
    (hp : ∀ n ≥ 1 , p (n + 1) = 1 - p n / 2) : 
    ∀ k ≥ 1 , (1 - p k) / 2 = 1 / 6 + 1 / (3 * (- 2) ^ k) := by
  
  -- First, transform the recurrence relation into a geometric sequence form
  have eq_recur : ∀ n ≥ 1 , p (n + 1) - 2 / 3 = - 1 / 2 * (p n - 2 / 3) := by
    intro n hn
    rw [hp n hn]
    ring
    
  -- Then, derive the closed-form expression for p(n) using strong induction
  have closed_form : ∀ n ≥ 1, p n = 2 / 3 + (1 / 3) * (- 1 / 2) ^ (n - 1) := by
    intro n hn
    induction' n using Nat.strongRec with n ih
    cases n with
    | zero => simp at hn  
    | succ n =>
      cases n with
      | zero => 
        simp [hp1]
        ring_nf  
      | succ n =>
        have n_geq_zero : n ≥ 0 := Nat.zero_le n
        specialize ih (n+1) (Nat.lt_succ_self (n+1))
        rw [hp (n+1)]
        rw [ih (Nat.succ_pos n)]
        · field_simp
          ring_nf
        · linarith

  -- Finally, use the closed-form to compute the desired probability
  intro k hk
  have pk_eq :∀ k ≥ 1 , p k = 2 / 3 + (1 / 3) * (- 1 / 2) ^ (k - 1) := by exact fun k a => closed_form k a
  rw [pk_eq]
  ring_nf
  · 
    -- Simplify the exponent term using properties of exponents
    have t₁: (-1 / 2) ^ (k - 1) * (- 1 / 6)=  (- 1 / 2) ^ k * (1 / 3 : ℝ) := by
      have t₂: (- 1 / 2) ^ k = ((- 1 / 2) ^ (k - 1)) * (-1 / 2 : ℝ) := 
      by
        refine Eq.symm 
          (pow_sub_one_mul (by exact
          Nat.not_eq_zero_of_lt hk) (- 1 / 2))
      rw[t₂] 
      refine Eq.symm (Mathlib.Tactic.Ring.mul_pf_left (- 1 / 2) (k - 1) (by ring))
    rw[t₁]
  · 
    linarith