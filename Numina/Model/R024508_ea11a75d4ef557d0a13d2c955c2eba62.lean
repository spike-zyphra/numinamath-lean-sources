import Mathlib

theorem number_theory_254585 :
    IsGreatest {n | ∃ m, m^2 = n^2 + 2007 * n} 1006009 := by

  constructor
  · -- Show that 1006009 is in {n | ∃ m, m^2 = n^2 + 2007 * n}.
    use 1007012
    all_goals
      norm_num
  · -- Show that 1006009 is greatest in {n | ∃ m, m^2 = n^2 + 2007 * n}.
    intro n hn
    rcases hn with ⟨m, hm⟩
    by_contra h'
    push_neg at h'
    -- Assume n > 1006009, derive a contradiction.
    have h1 : n > 1006009 := h'
    -- Assume n > 1006009, then m > n + 1003.
    have h2 : m > n + 1003 := by
      by_contra h
      push_neg at h
      have h3 : m ≤ n + 1003 := by linarith
      nlinarith [sq_nonneg (m - (n + 1003)), sq_nonneg (m + (n + 1003)), 
          h3, sq_nonneg (m - n), sq_nonneg ((n) + 1003)]
    -- Assume n > 1006009, then m > n + 1003, leads to contradiction.
    have h3 : m ≥ n + 1004 := by
      omega
    -- Assume n > 1006009, then m > n + 1003, leads to contradiction.
    nlinarith [sq_nonneg (m - (n + 1004)), sq_nonneg (m + (n + 1004)), 
        sq_nonneg (m - n), sq_nonneg (m - (n + 2007)), 
        h2, h3]