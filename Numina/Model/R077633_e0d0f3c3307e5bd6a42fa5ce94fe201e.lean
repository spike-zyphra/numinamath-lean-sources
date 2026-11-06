import Mathlib

theorem algebra_21811 : IsLeast {n | n ∈ Set.Icc 100 999 ∧ ∃ a, n = 100 * a + 10 * a + a ∧ 9 ∣ n} 333 := by
  constructor
  · -- We need to prove that 333 is in the set
    refine ⟨by norm_num, ?_⟩
    use 3
    all_goals norm_num
  · -- We need to prove that 333 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn1, ⟨a, rfl, hn2⟩⟩
    rcases hn1 with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : a < 3 := by nlinarith
    have h4 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    rcases h4 with (rfl | rfl | rfl)
    · -- Case a = 0
      norm_num at *
      all_goals omega
    · -- Case a = 1
      norm_num at *
      all_goals omega
    · -- Case a = 2
      norm_num at *
      all_goals omega