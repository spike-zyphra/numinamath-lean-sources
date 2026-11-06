import Mathlib

theorem number_theory_205089 :
    IsLeast {n | ∃ x y z : ℕ, n = x + y + z ∧ x * 3 + y * 5 + z * 7 = 130} 20 := by
  constructor
  · -- Show 20 is in the set.
    use 2, 1, 17
    all_goals norm_num
  · -- Show that 20 is the minimum element in the set.
    intro n hn
    rcases hn with ⟨x, y, z, h1, h2⟩
    by_contra h
    push_neg at h
    -- So n < 20
    have h3 : x + y + z < 20 := by
      linarith [h1, h]
    -- Now given x * 3 + y * 5 + z * 7 = 130
    -- We do exhaustive search. As x, y, z >= 0 and bounded, so equations must contradiction.
    have h4 : x ≤ 19 := by 
      omega
    have h5 : y ≤ 19 := by 
      omega
    have h6 : z ≤ 19 := by
      omega
    interval_cases x <;> interval_cases y <;> omega