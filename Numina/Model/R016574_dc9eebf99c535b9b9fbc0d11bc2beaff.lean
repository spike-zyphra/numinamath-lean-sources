import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190006 (x : ℝ) (hx : x ≠ 5) :
    (4 - x) / (x - 5) > 1 / (1 - x) ↔ x ∈ (Set.Ioo 1 3) ∪ (Set.Ioo 3 5) := by
  constructor
  · -- Forward direction: if (4 - x) / (x - 5) > 1 / (1 - x) then x ∈ (1, 3) ∪ (3, 5)
    intro h
    have h1 : x - 5 ≠ 0 := by
      intro h2
      apply hx
      linarith
    by_cases h2 : 1 - x = 0
    · -- Case where 1 - x = 0 (x = 1)
      have h3 : x = 1 := by linarith
      rw [h3] at h
      norm_num at h
    · -- Case where 1 - x ≠ 0 (x ≠ 1)
      have h2' : x ≠ 1 := by
        intro h3
        apply h2
        linarith
      have h3 : x - 5 ≠ 0 := by
        intro h4
        apply hx
        linarith
      have h4 : 1 - x ≠ 0 := by
        intro h5
        apply h2'
        linarith
      have h5 : ((4 - x) / (x - 5) - 1 / (1 - x)) > 0 := by linarith
      have h6 : ((4 - x) / (x - 5) - 1 / (1 - x)) = ((x - 3) ^ 2) / ((x - 5) * (1 - x)) := by
        field_simp [(show x - 5 ≠ 0 by assumption), (show 1 - x ≠ 0 by assumption)]
        ring
      rw [h6] at h5
      have h7 : ((x - 3) ^ 2) / ((x - 5) * (1 - x)) > 0 := h5
      apply div_pos_iff.mp at h7
      cases h7 with
      | inl h8 =>
        have h8a : (x - 3) ^ 2 > 0 := h8.1
        have h8b : (x - 5) * (1 - x) > 0 := h8.2
        have h8c : x ≠ 3 := by
          by_contra h8d
          have : (x - 3) ^ 2 = 0 := by
            rw [show x - 3 = 0 by linarith [h8d]]
            all_goals norm_num
          linarith
        have h8d : 1 < x := by nlinarith
        have h8e : x < 5 := by nlinarith
        by_cases h12 : x < 3
        · -- Case x < 3
          left
          exact ⟨by linarith, by linarith⟩
        · -- Case x ≥ 3
          have h13 : x > 3 := by 
            by_contra h14
            push_neg at h14
            have h14a : x = 3 := by linarith
            contradiction
          right
          exact ⟨by linarith, by linarith⟩
      | inr h9 =>
        exfalso
        nlinarith [sq_nonneg (x - 3)]
  · -- Reverse direction: if x ∈ (1, 3) ∪ (3, 5), then (4 - x) / (x - 5) > 1 / (1 - x)
    intro h
    rcases h with (h1 | h2)
    · -- Case x ∈ (1, 3)
      rcases h1 with ⟨h11, h12⟩
      have h2 : x - 5 < 0 := by linarith
      have h3 : 1 - x < 0 := by linarith
      have h4 : ( (4 - x) / (x - 5) - 1 / (1 - x) ) > 0 := by
        have h5 : ( (4 - x) / (x - 5) - 1 / (1 - x) ) = ( (x - 3) ^ 2 ) / ( (x - 5) * (1 - x) ) := by
          field_simp [(show x - 5 ≠ 0 by linarith), (show 1 - x ≠ 0 by linarith)]
          ring
        rw [h5]
        apply div_pos
        · -- Show (x - 3) ^ 2 > 0
          nlinarith
        · -- Show (x - 5) * (1 - x) > 0
          nlinarith
      linarith
    · -- Case x ∈ (3, 5)
      rcases h2 with ⟨h21, h22⟩
      have h2 : x - 5 < 0 := by linarith
      have h3 : 1 - x < 0 := by linarith
      have h4 : ( (4 - x) / (x - 5) - 1 / (1 - x) ) > 0 := by
        have h5 : ( (4 - x) / (x - 5) - 1 / (1 - x) ) = ( (x - 3) ^ 2 ) / ( (x - 5) * (1 - x) ) := by
          field_simp [(show x - 5 ≠ 0 by linarith), (show 1 - x ≠ 0 by linarith)]
          ring
        rw [h5]
        apply div_pos
        · -- Show (x - 3) ^ 2 > 0
          nlinarith
        · -- Show (x - 5) * (1 - x) > 0
          nlinarith
      linarith