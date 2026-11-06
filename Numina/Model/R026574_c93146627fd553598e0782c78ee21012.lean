import Mathlib

open Real Set

theorem algebra_221279 : IsLeast {x | ∃ t : ℝ, x = max (abs (t + 1)) (abs (t - 2))} (3 / 2) := by
  constructor
  · -- Show 3/2 is in the set
    use 1 / 2
    norm_num [abs, max_eq_left, max_eq_right]
    all_goals norm_num
  · -- Show that 3/2 is the least element
    intro x hx
    rcases hx with ⟨t, ht⟩
    by_contra h
    push_neg at h
    have h1 : x = max (abs (t + 1)) (abs (t - 2)) := ht
    rw [h1] at h
    -- Show that max (abs (t + 1)) (abs (t - 2)) >= 3/2
    have h2 : max (abs (t + 1)) (abs (t - 2)) < 3 / 2 := by linarith
    -- Assume the contradiction, showing it is false.
    -- So we need to show that both abs (t + 1) < 3 / 2 and abs (t - 2) < 3 / 2 leads to contradiction
    have h3 : abs (t + 1) < 3 / 2 := by
      by_contra h3
      push_neg at h3
      have h3' : abs (t + 1) ≥ 3 / 2 := by
        linarith
      have h4 : max (abs (t + 1)) (abs (t - 2)) ≥ abs (t + 1) := by
        apply le_max_left
      linarith
    have h4 : abs (t - 2) < 3 / 2 := by
      by_contra h4
      push_neg at h4
      have h4' : abs (t - 2) ≥ 3 / 2 := by
        linarith
      have h5 : max (abs (t + 1)) (abs (t - 2)) ≥ abs (t - 2) := by
        apply le_max_right
      linarith
    -- Now we have abs (t + 1) < 3 / 2 and abs (t - 2) < 3 / 2.
    -- This implies that $t$ must be in the intersection of the intervals $(-1 - 3/2, 2 + 3/2)$ and $(2 - 3/2, 1 + 3/2)$
    -- Let's find these intervals with `abs_lt.mp`
    have h5 : -3 / 2 < t + 1 := by linarith [abs_lt.mp h3]
    have h6 : t + 1 < 3 / 2 := by linarith [abs_lt.mp h3]
    have h7 : -3 / 2 < t - 2 := by linarith [abs_lt.mp h4]
    have h8 : t - 2 < 3 / 2 := by linarith [abs_lt.mp h4]
    -- Let's translate these to $t$'s bounds.
    -- So, from h5 and h6:
    -- $ -5/2 < t < 1/2 $
    -- From h7 and h8:
    -- $ 1/2 < t < 7/2 $
    -- So their intersection is empty. We show this with linarith.
    linarith