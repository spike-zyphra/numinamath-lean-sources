import Mathlib

theorem algebra_15491 :
    IsLeast {n | ∃ k l : ℕ, n = k * l ∧ k > 0 ∧ l > 0 ∧ k * 3 = l * 2} 6 := by
  constructor
  · -- Show 6 is in the set
    use 2, 3
    all_goals norm_num
  · -- Show 6 is minimal
    intro n hn
    rcases hn with ⟨k, l, h_eq, hk, hl, h_eq2⟩
    by_contra h
    push_neg at h
    have h1 : k ≤ 5 := by
      nlinarith [show k ≤ 5 by nlinarith [h_eq, h, hl, hk]]
    have h2 : l ≤ 5 := by
      nlinarith [show l ≤ 5 by nlinarith [h_eq, h, hl, hk]]
    interval_cases k <;> interval_cases l
    <;> omega