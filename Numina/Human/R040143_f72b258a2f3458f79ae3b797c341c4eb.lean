import Mathlib

open Finset

/-Let $S$ be the smallest subset of the integers with the property that $0 \in S$ and for any $x \in S$, we have $3 x \in S$ and $3 x+1 \in S$. Determine the number of non-negative integers in $S$ less than 2008.-/
theorem number_theory_608276 (S : Set ℕ) (hS : ∀ x ∈ S, 3 * x + 1 ∈ S ∧ 3 * x ∈ S)
    (hS1 : 0 ∈ S) (hS2 : ∀ T, 0 ∈ T → (∀ x ∈ T, 3 * x + 1 ∈ T ∧ 3 * x ∈ T) → S ⊆ T) :
    Set.ncard {x | x < 2008 ∧ x ∈ S} = 128 := by
-- Prove the key fact that $S$ is equal to the set of numbers whose $3$-adic digits have no $2$
  have key : S = {x | 2 ∉ Nat.digits 3 x} := by
    apply Set.eq_of_subset_of_subset
    -- Apply `hS2` to prove one side of the inclusion
    · apply hS2; simp
      · simp; intro x hx; by_cases h : x = 0
        · simp [h]
        constructor
        · norm_num [Nat.mul_add_div, Nat.mul_add_mod]
          exact hx
        rw [Nat.digits_eq_cons_digits_div]
        norm_num; exact hx
        all_goals omega
  -- Using strong induction to prove the other side of inclusion
    simp [Set.subset_def]; intro x
    induction x using Nat.strong_induction_on with
    | h x ih =>
      intro hx; by_cases h : x = 0
      · simp [h]; exact hS1
      rw [Nat.digits_eq_cons_digits_div] at hx
      simp at hx; specialize ih (x / 3) (by omega) hx.right
      rw [← Nat.div_add_mod x 3]; have := Nat.mod_lt x (show 3>0 by simp)
      interval_cases x % 3
      · simp; exact (hS (x / 3) ih).right
      · exact (hS (x / 3) ih).left
      simp at hx; simp; exact h
-- Use `native_decide` tactics to finish the goal
  suffices : {x | x < 2008 ∧ x ∈ S} = {x ∈ range 2008 | 2 ∉ Nat.digits 3 x}
  · rw [this, Set.ncard_coe_Finset]; native_decide
  simp [key]