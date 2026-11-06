import Mathlib

open Finset Real

/-Let $\pi$ be a permutation of the numbers from 2 through 2012. Find the largest possible value of $\log _{2} \pi(2) \cdot \log _{3} \pi(3) \cdots \log _{2012} \pi(2012)$.-/
theorem number_theory_609053 :
IsGreatest {m | ∃ p : Equiv.Perm (Icc 2 2012), m = ∏ i : Icc 2 2012, logb i (p i).val} 1 := by
-- We show that for any permutation $p$, the product in question is $1$
  have aux : ∀ p : Equiv.Perm (Icc 2 2012), ∏ i : Icc 2 2012, logb i (p i).val = 1 := by
    intro p; rw [prod_coe_sort_eq_attach]; simp only [logb]
    rw [prod_div_distrib, ← prod_coe_sort_eq_attach, ← prod_coe_sort_eq_attach]
    rw [Fintype.prod_equiv p _ (fun i : Icc 2 2012 => log i.val), div_self]
    rw [prod_coe_sort_eq_attach, prod_ne_zero_iff]; intro x hx
    rw [log_ne_zero]; have := x.2; rw [mem_Icc] at this; norm_cast
    split_ands; any_goals omega
    all_goals simp
-- The goal follows from aux automatically
  rw [IsGreatest, upperBounds]; simp at *; constructor
  · use 1; symm; apply aux
  intros; simp [aux]