import Mathlib

open Real Set

theorem algebra_251631 :
    IsLeast {x | ∃ a b : ℝ, x = max (max (|a + b|) (|a - b|)) (|1 - b|)} (1 / 2) := by 
  constructor 
  · -- Show 1/2 is in the set by choosing a = 0, b = 1/2
    use 0, 1 / 2 
    norm_num [abs]
    <;> norm_num
    <;> norm_num [abs]
    <;> norm_num [abs]
    <;> norm_num
  · -- Show that if x is in the set, then 1/2 ≤ x 
    intro x hx 
    rcases hx with ⟨a, b, hx⟩ 
    by_contra h
    push_neg at h
    have h1 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ 1 / 2 := by
      by_contra h3
      push_neg at h3
      have h2 : max (|a + b|) (|a - b|) < 1 / 2 := by
        by_contra h4
        push_neg at h4
        have h5 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ max (|a + b|) (|a - b|) := by
          exact le_max_left (max (|a + b|) (|a - b|)) (|1 - b|) 
        linarith [h4, h5, h3] 
      have h31 : |a + b| < 1 / 2 := by 
        have h4 : |a + b| < 1 / 2 := by 
          by_contra h4
          push_neg at h4
          have h5 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ |a + b| := by
            have : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ max (|a + b|) (|a - b|) := by
              exact le_max_left (max (|a + b|) (|a - b|)) (|1 - b|) 
            have h6 : max (|a + b|) (|a - b|) ≥ |a + b| := by 
              apply le_max_left
            linarith 
          linarith [h4, h5, h3] 
        simpa using h4 
      have h32 : |a - b| < 1 / 2 := by 
        by_contra h4
        push_neg at h4
        have h5 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ |a - b| := by
          have : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ max (|a + b|) (|a - b|) := by
            exact le_max_left (max (|a + b|) (|a - b|)) (|1 - b|) 
          have h6 : max (|a + b|) (|a - b|) ≥ |a - b| := by 
            apply le_max_right 
          linarith 
        linarith [h4, h5, h3] 
      have h33 : |1 - b| < 1 / 2 := by 
        by_contra h4
        push_neg at h4
        have h5 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ |1 - b| := by
          have h6 : max (max (|a + b|) (|a - b|)) (|1 - b|) ≥ |1 - b| := by 
            apply le_max_right 
          linarith 
        linarith [h4, h5, h3] 
      have h41 : -1 / 2 < a + b := by 
        linarith [abs_lt.mp h31]
      have h42 : a + b < 1 / 2 := by 
        linarith [abs_lt.mp h31] 
      have h43 : -1 / 2 < a - b := by 
        linarith [abs_lt.mp h32] 
      have h44 : a - b < 1 / 2 := by 
        linarith [abs_lt.mp h32] 
      have h45 : 1 - b > -1 / 2 := by 
        linarith [abs_lt.mp h33] 
      have h46 : 1 - b < 1 / 2 := by 
        linarith [abs_lt.mp h33] 
      have h47 : 1 / 2 < b := by linarith 
      have h48 : b < 3 / 2 := by linarith 
      have h49 : a < 0 := by 
        linarith [h47] 
      have h50 : a > 0 := by 
        linarith [h47] 
      linarith 
    linarith [h1, hx, h]