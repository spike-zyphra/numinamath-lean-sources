import Mathlib

open Real Set
open scoped BigOperators

/- 2. The numbers are $a_{1}=\log _{2}\left(3^{x}-1\right), a_{2}=\log _{4}\left(9^{x}-3^{x+1}+2\right)$ and $a_{3}=\log _{2}\left(3-3^{x}\right)$.
a) Determine all real values of $x$ for which all 3 numbers $a_{1}, a_{2}$, and $a_{3}$ are defined.

b) Determine all real values of $x$ for which $a_{1}+a_{3}=2 a_{2}$. -/
theorem algebra_104628 {x: ℝ} :  (0 < (3:ℝ)^x - 1 ∧ 0 < (9:ℝ)^x - (3:ℝ)^(x+1) + 2 ∧ 0 < 3 - (3:ℝ)^x) ↔ x ∈ Ioo (logb 3 2) (1) := by 
  -- Show inequality that will be handy later
  have ineq : logb 3 2 < x → 0 < x := by
    intro h
    trans logb 3 2
    . apply logb_pos <;> norm_num
    . exact h

  -- Factorise second inequality
  have factorisation : 0 < (9:ℝ)^x - (3:ℝ)^(x+1) + 2 ↔ 0 < ((3:ℝ)^x - 1) * (3 ^ x - 2) := by 
    have h : (9:ℝ)^x = ((3:ℝ)^x)^(2:ℝ) := by rw [<- rpow_mul (by positivity), mul_comm, rpow_mul (by positivity)]; ring_nf
    have h' : ((3: ℝ)^x)^2 - (3:ℝ)^x * 3 + 2 = ((3: ℝ)^x -1) * ((3:ℝ)^x -2) := by ring
    -- Rewrite accordingly
    rw [rpow_add (by positivity), h]
    norm_num
    rw [h']


  constructor
  --- '→' Assume inequalities and prove range for x
  . rintro ⟨ineq₁, ineq₂, ineq₃⟩

    rw [mem_Ioo]

    constructor
    -- Prove lower bound using ineq₂
    . rw [factorisation] at ineq₂

      -- Now have factorised inequality so argue by cases
      rw [mul_pos_iff] at ineq₂
      rcases ineq₂ with case₁ | case₂
      -- Prove goal in this case
      . rcases case₁ with ⟨bound₁, bound₂⟩
        rw [sub_pos] at bound₂
        refine (logb_lt_iff_lt_rpow ?_ ?_).mpr bound₂
        all_goals norm_num
       -- Not possible: reach contradiction
      . rcases case₂ with ⟨bound₁, bound₂⟩
        exfalso
        linarith

    --- Prove upper bound using ineq₃
    . rw [sub_pos, show (3:ℝ) = (3:ℝ)^(1:ℝ) by norm_num, show ((3:ℝ)^(1:ℝ))^x = (3:ℝ)^x by ring_nf] at ineq₃
      have : (1:ℝ) < (3:ℝ) := by linarith
      rw [rpow_lt_rpow_left_iff this] at ineq₃
      exact ineq₃
    
  -- '←' Assume bound for x and prove inequalities
  . rintro ⟨bound1, bound2⟩
    constructor
    -- Prove first inequality
    . simp_all
      refine one_lt_rpow ?_ ?_
      . norm_num
      . exact ineq
    . constructor
      -- Prove second inequality
      . rw [factorisation]
        rw [mul_pos_iff]

        left -- Prove that both terms are positive
        constructor
        . simp_all
          apply (one_lt_rpow_iff ?_).mpr ?_ <;> norm_num; exact ineq
        . simp_all
          rw [<- logb_lt_iff_lt_rpow ?_ ?_] <;> norm_num
          exact bound1
          
      -- Prove third inequality
      . simp_all
        refine rpow_lt_self_of_one_lt ?_ bound2
        norm_num