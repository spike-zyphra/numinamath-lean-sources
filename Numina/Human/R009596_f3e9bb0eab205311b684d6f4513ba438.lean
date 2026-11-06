import Mathlib

theorem number_theory_47011 (n : ℕ) (h : n > 0) :
    734851474594578436096 = n ^ 6 ↔ n = 3004 := by
  constructor
  swap
  . -- verify that 3004 is the n
    intro hn
    subst hn
    norm_num
  . intro h1
    have h2 : n = 3004 := by
      have h3 : n^6 = 734851474594578436096 := by linarith
      have h4 : n = 3004 := by
        have h5 : n ≤ 3004 := by
          by_contra h
          push_neg at h
          have h6 : n^6 > 3004^6 := by
            apply Nat.pow_lt_pow_left
            all_goals linarith
          linarith
        have h7 : 3004 ≤ n := by
          by_contra h
          push_neg at h
          have h8 : n^6 < 3004^6 := by
            apply Nat.pow_lt_pow_left
            all_goals linarith
          linarith
        omega
      exact h4
    exact h2