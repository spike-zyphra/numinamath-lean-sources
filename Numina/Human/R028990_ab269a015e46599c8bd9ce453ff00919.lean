import Mathlib

open Real Set
open scoped BigOperators Function

theorem algebra_269879 {f : ℝ → ℝ} (hf : ∀ x, f x = f (- x)) (h : {x | f x = 0}.encard = 4) :
    ∑ᶠ x ∈ {x | f x = 0}, x = 0 := by 
  -- if x ∈ {x | f x = 0 } then -x ∈ {x | f x = 0}
  have h1 : ∀ x, x ∈ {x | f x = 0} ↔ -x ∈ {x | f x = 0} := by 
    intro x
    constructor 
    intro hx
    rw [Set.mem_setOf_eq] at hx ⊢
    specialize hf x
    rw [←hf]
    simpa
    intro hx
    rw [Set.mem_setOf_eq] at hx ⊢
    specialize hf x
    rw [hf]
    simpa
  -- and sum over a finite set is well defined on any property which contains -x for every x in it.
  have eq_aux : ∑ᶠ (x : ℝ) (_ : x ∈ {x | f x = 0}), x = ∑ᶠ (x : ℝ) (_ : x ∈ {x | f x = 0}), - x := by 
    refine finsum_eq_of_bijective ?_ ?_ ?_
    · intro x 
      exact -x
    · unfold Function.Bijective
      constructor
      exact neg_injective
      exact neg_surjective
    · 
      simp
      exact fun x => finsum_congr_Prop (congrFun (congrArg Eq (hf x)) 0) (congrFun rfl)
  have eq_aux2 : ∑ᶠ (x : ℝ) (_ : x ∈ {x | f x = 0}), - x = - ∑ᶠ (x : ℝ) (_ : x ∈ {x | f x = 0}), x := by 
    refine finsum_mem_neg_distrib (fun x => x) ?_
    apply Set.encard_ne_top_iff.mp
    rw [h]
    simp
  have eq_aux3 : 2 * (∑ᶠ (x : ℝ) (_ : x ∈ {x | f x = 0}), x) = 0 := by
    nlinarith
  nlinarith