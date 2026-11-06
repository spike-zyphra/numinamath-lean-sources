import Mathlib

open Real Set

theorem inequalities_174613 :
    IsGreatest {C : ℝ | ∀ a b, max (max (|a + b|) (|a - b|)) (|2006 - b|) ≥ C} 1003 := by
  constructor
  · -- Show 1003 is in the set
    intro a b
    by_contra h
    push_neg at h
    -- Assume the maximum is less than 1003, reach contradiction
    have h1 : max (max (|a + b|) (|a - b|)) (|2006 - b|) < 1003 := h
    have h2 : |a + b| < 1003 := by
      have h3 : |a + b| ≤ max (max (|a + b|) (|a - b|)) (|2006 - b|) := by
        simp
      have h4 : max (max (|a + b|) (|a - b|)) (|2006 - b|) < 1003 := h
      linarith
    have h3 : |a - b| < 1003 := by
      have h4 : |a - b| ≤ max (max (|a + b|) (|a - b|)) (|2006 - b|) := by
        simp
      have h5 : max (max (|a + b|) (|a - b|)) (|2006 - b|) < 1003 := h
      linarith
    have h4 : |2006 - b| < 1003 := by
      have h5 : |2006 - b| ≤ max (max (|a + b|) (|a - b|)) (|2006 - b|) := by
        simp
      have h6 : max (max (|a + b|) (|a - b|)) (|2006 - b|) < 1003 := h
      linarith
    cases' abs_lt.mp h2 with h2_neg h2_pos
    cases' abs_lt.mp h3 with h3_neg h3_pos
    cases' abs_lt.mp h4 with h4_neg h4_pos
    linarith
  · -- Show it's greatest
    intro c hc
    have h1 : ∀ a b, max (max (|a + b|) (|a - b|)) (|2006 - b|) ≥ c := hc
    have h2 := h1 0 1003
    norm_num [abs_of_nonneg, abs_of_nonpos] at h2 ⊢
    all_goals linarith