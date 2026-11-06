import Mathlib

theorem number_theory_132537 : IsGreatest {x | ¬∃ n m, x = 3 * n + 11 * m} 19 := by
  constructor
  · -- We verify that 19 is indeed in the set
    norm_num
    all_goals omega
  · -- Next, we need to show that for any x in the set, x ≤ 19
    intro x h
    have h1 : ¬∃ n m, x = 3 * n + 11 * m := by
      simpa using h
    by_contra h2
    push_neg at h2
    have h2' : x > 19 := by
      omega
    have h4 : ∃ n m, x = 3 * n + 11 * m := by
      have h5 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by
        omega
      rcases h5 with (h5 | h5 | h5)
      · -- Case where x % 3 = 0
        use x / 3, 0
        omega
      · -- Case where x % 3 = 1
        use (x - 22) / 3, 2
        omega
      · -- Case where x % 3 = 2
        use (x - 11) / 3, 1
        omega
    contradiction