import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_945 {f : ℝ → ℝ} (hf : f = λ x => (x - 3) / (x - 4)) : {x | f ⁻¹' {x} = ∅} = {1} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume f⁻¹' {x} = ∅, we need to show x = 1
    intro h 
    by_contra hx 
    push_neg at hx
    have h1 : x ≠ 1 := hx
    have h2 : f ((3 - 4 * x) / (1 - x)) = x := by
      rw [hf]
      have e3 : 1 - x ≠ 0 := by
        intro e
        apply h1
        linarith
      -- Let's compute `f((3 - 4*x)/(1 - x))` directly and check that it equals `x`
      -- `f(y) = (y - 3)/(y - 4)`
      -- So `f((3 - 4*x)/(1 - x)) = ((3 - 4*x)/(1 - x) - 3)/((3 - 4*x)/(1 - x) - 4)`
      -- Compute the numerator: `((3 - 4*x)/(1 - x) - 3) = (3 - 4*x - 3*(1 - x))/(1 - x) = (3 - 4*x - 3 + 3*x)/(1 - x) = (-x)/(1 - x)`
      -- Compute the denominator: `((3 - 4*x)/(1 - x) - 4) = (3 - 4*x - 4*(1 - x))/(1 - x) = (3 - 4*x - 4 + 4*x)/(1 - x) = (-1)/(1 - x)`
      -- So the entire expression is: `(-x/(1 - x))/(-1/(1 - x)) = x`
      -- So need tactics to compute this.
      have h3 : ((3 - 4 * x) / (1 - x) - 3) / ((3 - 4 * x) / (1 - x) - 4) = x := by 
        field_simp [e3]
        <;> ring_nf 
      exact h3
    have h3 : ((3 - 4 * x) / (1 - x) : ℝ) ∈ f ⁻¹' {x} := by 
      simp [Set.mem_preimage, h2]
    have h4 : f ⁻¹' {x} = ∅ := by 
      simpa using h
    rw [h4] at h3
    simp at h3
  · -- Assume x = 1, we need to show f⁻¹' {x} = ∅
    intro h 
    rw [h] 
    ext y 
    simp [hf]
    by_cases h : y - 4 = 0 
    · -- When y - 4 = 0 
      rw [h] 
      all_goals norm_num 
    · -- When y - 4 ≠ 0 
      have hx3 : (y - 3 : ℝ) / (y - 4 : ℝ) ≠ 1 := by 
        by_contra hneq 
        have h4 : y - 4 ≠ 0 := by 
          intro h7 
          apply h 
          linarith 
        have h5 : y - 3 = y - 4 := by 
          field_simp at hneq ⊢ 
          all_goals linarith 
        linarith 
      simp [hx3]