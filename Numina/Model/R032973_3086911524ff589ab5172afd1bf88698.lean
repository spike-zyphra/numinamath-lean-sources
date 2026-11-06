import Mathlib
open Nat

namespace number_theory_214071

def gp_sum (A p n : ℕ) : ℕ := A * (p ^ n - 1) / (p - 1)

def valid_score (k n : ℕ) : Prop :=
  ∃ A p : ℕ, p > 1 ∧ A > 0 ∧ gp_sum A p n = k ∧ A * p ^ (n - 1) ≤ k

theorem number_theory_214071_1 : valid_score 1989 2 ∧ valid_score 1989 3 := by
  
  constructor
  · 
    use 663, 2
    simp only [gp_sum]
    norm_num
  · 
    use 153, 3
    simp only [gp_sum]
    norm_num

theorem number_theory_214071_2 : valid_score 1988 2 ∧ valid_score 1988 3 := by 
  constructor
  · -- Show valid_score 1988 2
    use 497, 3
    simp only [gp_sum]
    norm_num
  · -- Show valid_score 1988 3
    use 284, 2
    simp only [gp_sum]
    norm_num