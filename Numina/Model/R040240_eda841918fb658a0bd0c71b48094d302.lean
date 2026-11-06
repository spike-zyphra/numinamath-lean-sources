import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20716 (p : ℝ) (hp : 0 < p ∧ p < 15) :
    IsLeast {x | ∃ t ∈ Icc p 15, x = abs (t - p) + abs (t - 15) + abs (t - p - 15)} 15 := by
  constructor
  · -- Show that 15 is in the set, by choosing t = 15.
    use 15
    constructor
    · -- Show 15 ∈ [p, 15]
      exact ⟨by linarith [hp.2], by norm_num⟩
    · -- Show that when t = 15, the value is 15
      have hp1 : 0 < p := hp.1
      have hp2 : p < 15 := hp.2
      have hp3 : p > 0 := hp1
      have hp4 : 15 - p > 0 := by linarith
      have h1 : abs (15 - p) = 15 - p := by
        rw [abs_of_pos]
        linarith
      have h2 : abs ((15 : ℝ) - (15 : ℝ)) = 0 := by
        norm_num [abs_zero]
      have h3 : abs ((15 - p - 15 : ℝ)) = p := by
        have h4 : (15 - p - 15 : ℝ) = -p := by
          linarith
        rw [h4]
        rw [abs_of_neg (by linarith)]
        all_goals linarith
      -- The original expression is abs (t - p) + abs (t - 15) + abs (t - p - 15)
      -- Substituting t = 15
      have h5 : abs ((15 : ℝ) - p) = abs (15 - p) := by
        ring_nf
      have h6 : abs ((15 : ℝ) - (15 : ℝ)) = abs ((15 : ℝ) - (15 : ℝ)) := by
        ring_nf
      have h7 : abs ((15 : ℝ) - p - 15) = abs ((15 - p - 15 : ℝ)) := by
        ring_nf
      rw [h5, h6, h7]
      rw [h1, h2, h3]
      all_goals linarith
  · -- Show that 15 is the least element in the set
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    rcases ht with ⟨ht1, ht2⟩
    have hp1 : 0 < p := hp.1
    have hp2 : p < 15 := hp.2
    have h1 : abs (t - p) = t - p := by
      rw [abs_of_nonneg]
      linarith
    have h2 : abs (t - 15) = 15 - t := by
      rw [abs_of_nonpos]
      linarith
      all_goals linarith
    have h3 : abs (t - p - 15) = p + 15 - t := by
      have h11 : t - p - 15 ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos h11]
      all_goals linarith
    rw [h1, h2, h3]
    all_goals linarith