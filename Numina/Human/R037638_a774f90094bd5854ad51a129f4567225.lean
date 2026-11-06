import Mathlib

open Real Set
open scoped Real

theorem algebra_634415 {α : ℝ} (ha : ¬ ∃ k : ℤ, α = k * π / 2) :
    (sin α + tan α) / (cos α + 1 / tan α) > 0 := by 
  have neq1 : tan α ≠ 0 := by 
    refine tan_ne_zero_iff.mpr ?_
    simp at ha
    intro k
    obtain ha' := ha k
    exact fun a => ha k (id (Eq.symm a))
  have neq2 : sin α ≠ 0 := by 
    refine sin_ne_zero_iff.mpr ?_
    simp at ha
    intro k
    obtain ha' := ha (2 * k)
    norm_num at ha'
    by_contra hc
    rw [←hc] at ha'
    apply ha'
    field_simp
    ring
  have neq3 : (sin α + 1) ≠ 0 := by 
    have aux : sin α ≠  - 1 := by 
      by_contra h'
      obtain ⟨k, hk⟩ := (Real.sin_eq_neg_one_iff).mp h'
      simp at ha
      obtain hm := ha (4 * k - 1)
      apply hm
      rw [←hk]
      field_simp
      ring
    by_contra hc
    have sineq : sin α = -1 := by nlinarith
    exact aux sineq
  have neq5 : cos α ≠ 0 :=by 
    refine cos_ne_zero_iff.mpr ?_
    simp at ha
    intro k
    obtain ha' := ha (2 * k + 1)
    by_contra hc
    apply ha'
    rw [hc]
    field_simp
    
  have neq4 : cot α ≠ 0 := by
    rw [cot_eq_cos_div_sin α]
    rw [div_ne_zero_iff]
    constructor
    · simpa
    · simpa
  calc 
    _ = (tan α * (cos α + 1)) / (cot α * (sin α + 1)) := by 
      have aux : (sin α + tan α) = (tan α * (cos α + 1))  := by 
        ring_nf
        conv => 
          rhs; rw [add_comm]
        congr
        refine Eq.symm (tan_mul_cos ?_)
        refine cos_ne_zero_iff.mpr ?_
        intro k
        simp at ha
        by_contra h'
        obtain hm := ha (2 * k + 1)
        apply hm
        aesop
      have aux2 : (cos α + 1 / tan α) = (cot α * (sin α + 1)):= by
        ring_nf
        conv =>
          rhs; rw [add_comm]
        congr
        have : cot α = cos α / sin α := by exact cot_eq_cos_div_sin α
        rw [this]
        field_simp
        rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
        field_simp
      rw [aux, aux2]
    _ = ((tan α) ^ 2 * (cos α + 1) ) / (sin α + 1) := by 
      refine (div_eq_div_iff ?_ ?_).mpr ?_
      aesop      
      simpa
      rw [cot_eq_cos_div_sin α]
      field_simp
      nth_rw 2 [← Real.tan_mul_cos neq5]
      ring
    _ > 0 := by 
      have pos1 : tan α ^ 2> 0 := by 
        exact pow_two_pos_of_ne_zero neq1
      have pos2 : cos α + 1 > 0 := by 
        have cosge : cos α ≥ -1 := by exact neg_one_le_cos α
        have cosneq : cos α ≠ -1 := by 
          by_contra h'
          obtain ⟨k, hk⟩ := (Real.cos_eq_neg_one_iff).mp h'
          simp at ha
          obtain hm := ha (4 * k + 2)
          apply hm
          aesop
        apply lt_of_le_of_ne (by linarith)
        by_contra hc
        have aux : cos α = -1 := by nlinarith
        exact cosneq aux
      have pos3 : sin α + 1 > 0 := by 
        have singe : sin α ≥ -1 := by exact neg_one_le_sin α
        have sinneq : sin α ≠ -1 := by 
          by_contra h'
          obtain ⟨k, hk⟩ := (Real.sin_eq_neg_one_iff).mp h'
          simp at ha
          obtain hm := ha (4 * k - 1)
          apply hm
          rw [←hk]
          field_simp
          ring
        apply lt_of_le_of_ne (by linarith)
        by_contra hc
        have aux : sin α = -1 := by nlinarith
        exact sinneq aux
      positivity