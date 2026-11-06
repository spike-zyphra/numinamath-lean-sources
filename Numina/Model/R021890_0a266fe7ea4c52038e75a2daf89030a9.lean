import Mathlib

theorem number_theory_6888 (x : ℤ) (hx : 11*x≡369 [ZMOD 17]) :
    IsLeast {n | ∃ x : ℤ, 11*x≡369 [ZMOD 17] ∧ n=|x|} 2 := by
  constructor
  · -- Show 2 is in the set.
    use -2
    native_decide
  · -- Show it's minimal.
    intro n hn
    rcases hn with ⟨x, hx1, hn⟩
    by_contra h
    push_neg at h
    have h2 : n < 2 := by 
      omega
    have h3 : |x| < 2 := by 
      omega
    have h4 : x ≥ -1 := by
      cases' abs_lt.mp h3 with h5 h6
      omega
    have h5 : x ≤ 1 := by
      cases' abs_lt.mp h3 with h6 h7
      omega
    interval_cases x <;> norm_num [Int.ModEq] at hx1
    all_goals linarith