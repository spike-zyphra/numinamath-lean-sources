import Mathlib
open Real

theorem algebra_9094 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = - f x)
  (hpos : ∀ x > 0, f x = logb 2 x) :
  {x | f x > 0} = {x | 1 < x} ∪ {x | -1 < x ∧ x < 0} := by 
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume f(x) > 0, prove x ∈ {x | 1 < x} ∪ {x | -1 < x ∧ x < 0}
    intro h
    by_cases h1 : x > 0
    · -- x > 0
      have h2 : f x = logb 2 x := hpos x h1
      rw [h2] at h
      left
      have h3 : 1 < x := by
        by_contra h3
        push_neg at h3
        have h4 : x ≤ 1 := by linarith
        have h5 : logb 2 x ≤ logb 2 1 := by
          apply Real.logb_le_logb_of_le
          all_goals linarith
        have h6 : logb 2 1 = 0 := by
          rw [logb_one]
        have h7 : logb 2 x ≤ 0 := by linarith [h5, h6]
        linarith
      linarith
    by_cases h1' : x = 0
    · -- x = 0
      rw [h1'] at h
      have h4 : f 0 = 0 := by
        have h5 : f (-0) = - f 0 := hf 0
        simp at h5 ⊢
        linarith
      linarith [h4, h]
    · -- x < 0
      have h2 : x < 0 := by
        by_contra h2
        push_neg at h2
        have h3 : x ≥ 0 := by linarith
        have h4 : x = 0 := by linarith [h1', h3]
        contradiction
      -- Assume f(x) > 0, prove -1 < x and x < 0
      have h4 : f x = - f (-x) := by
        specialize hf x
        linarith
      have h5 : f (-x) = logb 2 (-x) := hpos (-x) (by nlinarith)
      rw [h4, h5] at h
      right
      have h6 : 0 < -x := by nlinarith
      have h7 : -x < 1 := by
        by_contra h7
        push_neg at h7
        have h8 : logb 2 (-x) ≥ logb 2 1 := by
          apply Real.logb_le_logb_of_le
          all_goals nlinarith
        have h9 : logb 2 1 = 0 := by
          rw [logb_one]
        have h10 : logb 2 (-x) ≥ 0 := by nlinarith [h8, h9]
        nlinarith
      constructor
      · -- Prove -1 < x
        nlinarith
      · -- Prove x < 0
        nlinarith
  · -- Assume x ∈ {x | 1 < x} ∪ {x | -1 < x ∧ x < 0}, prove f(x) > 0
    rintro (h1 | h2)
    · -- 1 < x
      have h1' : x > 0 := by nlinarith
      have h2 : f x = logb 2 x := hpos x h1'
      have h3 : logb 2 x > 0 := by
        have h4 : x > 1 := by linarith
        have h5 : logb 2 x > logb 2 1 := by
          apply Real.logb_lt_logb
          all_goals linarith
        have h6 : logb 2 1 = 0 := by
          rw [logb_one]
        linarith
      rw [h2]
      linarith
    · -- -1 < x ∧ x < 0
      rcases h2 with ⟨h1', h2'⟩
      have h3 : x < 0 := by linarith
      have h4 : f x = - f (-x) := by
        specialize hf x
        linarith
      have h5 : -x > 0 := by nlinarith
      have h6 : f (-x) = logb 2 (-x) := hpos (-x) h5
      rw [h4, h6]
      have h7 : logb 2 (-x) < 0 := by
        have h8 : -x < 1 := by nlinarith
        have h9 : logb 2 (-x) < logb 2 1 := by
          apply Real.logb_lt_logb
          all_goals nlinarith
        have h10 : logb 2 1 = 0 := by
          rw [logb_one]
        linarith [h9, h10]
      linarith