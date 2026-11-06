import Mathlib

open Set Real

theorem inequalities_321832 {x : ℝ} (hx : abs (x - 2) ≤ 1) :
    (x - 5) / (2 - x) > 0 ↔ 2 < x ∧ x ≤ 3 := by 
  constructor
  · -- Assume (x - 5) / (2 - x) > 0, prove 2 < x ∧ x ≤ 3
    intro h
    have h1 : 1 ≤ x ∧ x ≤ 3 := by
      constructor
      · -- Proof of 1 ≤ x using abs_le
        linarith [abs_le.mp hx]
      · -- Proof of x ≤ 3 using abs_le
        linarith [abs_le.mp hx]
    
    have h2 : 2 < x := by 
      by_contra h2
      push_neg at h2
      have h4 : x ≤ 2 := by linarith
      have h5 : 2 - x ≥ 0 := by linarith

      have h8 : (x - 5) / (2 - x) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Proof of x - 5 ≤ 0
          linarith
        · -- Proof of 2 - x ≥ 0
          linarith
      linarith

    have h3 : x ≤ 3 := h1.2
    exact ⟨h2, h3⟩
    
  · -- Assume 2 < x ∧ x ≤ 3, prove (x - 5) / (2 - x) > 0
    intro h
    have h1 : 1 ≤ x ∧ x ≤ 3 := by
      constructor
      · -- Proof of 1 ≤ x from 2 < x ∧ x ≤ 3
        linarith [h.1, h.2]
      · -- Proof of x ≤ 3 from hypothesis
        linarith [h.2]
    
    have h2 : 2 < x := h.1
    have h3 : x ≤ 3 := h.2
    
    have h4 : 2 - x < 0 := by linarith
    have h5 : x - 5 < 0 := by linarith
    apply div_pos_of_neg_of_neg
    all_goals linarith