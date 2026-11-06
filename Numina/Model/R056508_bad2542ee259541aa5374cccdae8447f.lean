import Mathlib

theorem algebra_312764 (a : ℕ → ℝ) (ha1 : a 1 = 2) (han : ∀ n > 0, a (n + 1) - 2 * a n = 2 ^ (n + 1)) :
    IsLeast {n | 0 < n ∧ a n > 10} 3 := by
  -- Show 3 is in the set
  constructor
  · -- Verify 3 is in the set {n | 0 < n ∧ a n > 10}
    constructor
    · norm_num
    · -- Compute a 3 and prove a 3 > 10
      have ha2 : a 2 = 8 := by
        have h2 := han 1 (by norm_num)
        norm_num at h2
        linarith [ha1]
      have ha3 : a 3 = 24 := by
        have h3 := han 2 (by norm_num)
        norm_num at h3
        linarith [ha2]
      linarith [ha3]
  · -- Show no element less than 3 is in the set
    intro n hn
    have h1 : 0 < n := hn.1
    have h2 : a n > 10 := hn.2
    by_contra h
    push_neg at h
    have h3 : n = 1 ∨ n = 2 := by 
      omega
    rcases h3 with (rfl | rfl)
    · -- Case n = 1
      linarith [ha1]
    · -- Case n = 2
      have ha2 : a 2 = 8 := by
        have h2 := han 1 (by norm_num)
        norm_num at h2
        linarith [ha1]
      linarith [ha2]