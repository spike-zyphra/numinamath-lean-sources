import Mathlib

theorem number_theory_262379 :
    IsLeast {n | ∃ r s t : ℕ, r > 0 ∧ s > 0 ∧ t > 0 ∧ r * s * t = 1230 ∧ n = r + s + t} 52 := by 
  constructor
  · -- Show 52 is in the set.
    use 5, 6, 41
    all_goals norm_num
  · -- Show no smaller element is in the set.
    intro n hn
    rcases hn with ⟨r, s, t, hr, hs, ht, h_eq1, h_eq2⟩
    by_contra h
    push_neg at h
    have h9 : r ≤ 50 := by
      omega
    have h10 : s ≤ 50 := by
      omega
    have h11 : t ≤ 50 := by
      omega
    interval_cases r <;> interval_cases s <;> omega