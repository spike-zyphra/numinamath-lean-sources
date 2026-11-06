import Mathlib

open Real Set
open scoped BigOperators

/- # Problem 6.

B-1

Find the minimum value of the expression $4 x+9 y+\frac{1}{x-4}+\frac{1}{y-5}$ given that $x>4$ and $y>5$. -/
theorem algebra_205642 :
  IsLeast {t : ℝ | ∃ x y, x > 4 ∧ y > 5 ∧ t = 4 * x + 9 * y + 1 / (x - 4) + 1 / (y - 5)} 71 := by
    set S := {t : ℝ | ∃ x y, x > 4 ∧ y > 5 ∧ t = 4 * x + 9 * y + 1 / (x - 4) + 1 / (y - 5)}
    unfold IsLeast
    constructor
    refine mem_setOf.mpr ?_
    --Clearly 9/2 and 16/3 are witnesses
    use 9 / 2, 16 / 3
    norm_num
    refine mem_setOf.mpr ?_
    intro a H
    rcases H with ⟨x, y, hxy⟩
    obtain ⟨h1, h2, h3⟩ := hxy
    --We'll now show that 4 * x + 9 * y + 1 / (x - 4) + 1 / (y - 5) ≥ 71.
    --First manipulate the LHS and obtain the following.
    have rearrange1 : 4 * x + 9 * y + 1 / (x - 4) + 1 / (y - 5) = 4 * x - 16 + 4 / (4 * x - 16) + 9 * y - 45 + 9 / (9 * y - 45) + 61 := by
      have h1 : 4 * x - 16 ≠ 0 := by linarith
      have h2 : 9 * y - 45 ≠ 0 := by linarith
      have h3 : 4 / (4 * x - 16) = 1 / (x - 4) := by
        refine (div_eq_div_iff h1 ?_).mpr ?_
        linarith
        ring_nf
      have h4 : 9 / (9 * y - 45) = 1 / (y - 5) := by
        refine (div_eq_div_iff h2 ?_).mpr ?_
        linarith
        ring_nf
      linarith
    --Next we show 4x - 16 + 4 / (4x - 16) ≥ 2 sqrt(4) = 4; This can be shown using the AM-GM inequality.
    --We'll apply the theorem `two_mul_le_add_sq`.
    --First rewrite 4x - 16 as (Real.sqrt (4x - 16))^2
    have rearrange2 : 4 * x - 16 = (Real.sqrt (4 * x - 16))^2 := by
      refine Eq.symm (sq_sqrt ?_)
      linarith
    --Next rewrite 9 * y - 45 as (Real.sqrt (9 * y - 45))^2
    have rearrange3 : 9 * y - 45 = (Real.sqrt (9 * y - 45))^2 := by
      refine Eq.symm (sq_sqrt ?_)
      linarith
    --Now we show the following inequality.
    have ineq1 : (4 * x - 16) + 4 / (4 * x - 16) ≥ 4 := by
      have ineq11 : 2 * (Real.sqrt (4 * x - 16)) * (2 / (Real.sqrt (4 * x - 16))) ≤ (Real.sqrt (4 * x - 16))^2 + (2 / (Real.sqrt (4 * x - 16)))^2 := by
        apply two_mul_le_add_sq (Real.sqrt (4 * x - 16)) (2 / Real.sqrt (4 * x - 16))
      --We'll simplify the LHS of ineq11. Clearly it's 4.
      have LHS : 2 * (Real.sqrt (4 * x - 16)) * (2 / (Real.sqrt (4 * x - 16))) = 4 := by
        calc
          _ = 2 * 2 * (Real.sqrt (4 * x - 16)) * (1 / (Real.sqrt (4 * x - 16))) := by ring
          _ = 4 * ((Real.sqrt (4 * x - 16)) * (1 / (Real.sqrt (4 * x - 16)))) := by ring
          _ = 4 * 1 := by
            have : (Real.sqrt (4 * x - 16)) * (1 / (Real.sqrt (4 * x - 16))) = 1 := by
              refine mul_one_div_cancel ?_
              refine sqrt_ne_zero'.mpr ?_
              linarith
            rw [this]
          _ = 4 := by norm_num
      --We'll simplify the RHS.
      have RHS1 : (Real.sqrt (4 * x - 16))^2 = 4 * x - 16 := by exact id (Eq.symm rearrange2)
      have RHS2 : (2 / (Real.sqrt (4 * x - 16)))^2 = 4 / (4 * x - 16) := by
        calc
          _ = 2^2 / (Real.sqrt (4 * x - 16))^2 := by ring
          _ = 4 / (4 * x - 16) := by
            rw [rearrange2]
            norm_num
      --Now let's rewrite ineq11 using LHS, RHS1, and RHS2.
      rw [LHS, RHS1, RHS2] at ineq11
      exact ineq11
    --Next we show this inequality.
    have ineq2 : (9 * y - 45) + 9 / (9 * y - 45) ≥ 6 := by
      have ineq11 : 2 * (Real.sqrt (9 * y - 45)) * (3 / (Real.sqrt (9 * y - 45))) ≤ (Real.sqrt (9 * y - 45))^2 + (3 / (Real.sqrt (9 * y - 45)))^2 := by
        apply two_mul_le_add_sq (Real.sqrt (9 * y - 45)) (3 / Real.sqrt (9 * y - 45))
      --We'll simplify the LHS of ineq11. Clearly it's 4.
      have LHS : 2 * (Real.sqrt (9 * y - 45)) * (3 / (Real.sqrt (9 * y - 45))) = 6 := by
        calc
          _ = 2 * 3 * (Real.sqrt (9 * y - 45)) * (1 / (Real.sqrt (9 * y - 45))) := by ring
          _ = 6 * ((Real.sqrt (9 * y - 45)) * (1 / (Real.sqrt (9 * y - 45)))) := by ring
          _ = 6 * 1 := by
            have : (Real.sqrt (9 * y - 45)) * (1 / (Real.sqrt (9 * y - 45))) = 1 := by
              refine mul_one_div_cancel ?_
              refine sqrt_ne_zero'.mpr ?_
              linarith
            rw [this]
          _ = 6 := by norm_num
      --We'll simplify the RHS.
      have RHS1 : (Real.sqrt (9 * y - 45))^2 = 9 * y - 45 := by exact id (Eq.symm rearrange3)
      have RHS2 : (3 / (Real.sqrt (9 * y - 45)))^2 = 9 / (9 * y - 45) := by
        calc
          _ = 3^2 / (Real.sqrt (9 * y - 45))^2 := by ring
          _ = 9 / (9 * y - 45) := by
            rw [rearrange3]
            norm_num
      --Now let's rewrite ineq11 using LHS, RHS1, and RHS2.
      rw [LHS, RHS1, RHS2] at ineq11
      exact ineq11
    --Finally, we close the goal using `linarith`.
    linarith