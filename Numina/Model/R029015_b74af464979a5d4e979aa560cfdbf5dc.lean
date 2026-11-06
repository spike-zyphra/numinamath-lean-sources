import Mathlib

theorem algebra_200941 (n : ℕ) (hn : n > 0) :
    IsSquare (n^2 + 5 * n + 13) ↔ n = 4 := by
  constructor
  · -- Assume IsSquare (n^2 + 5 * n + 13), prove n = 4
    intro h
    rcases h with ⟨r, hr⟩
    by_cases h1 : n ≤ 4
    · -- n ≤ 4
      interval_cases n <;> try { 
        { 
          have h2 : r ≤ 8 := by nlinarith
          interval_cases r <;> all_goals { omega }
        }
      }
    · -- n > 4
      have h2 : n > 4 := by omega
      -- Now, we need to show a contradiction
      have h4 : r > n := by
        by_contra h
        push_neg at h
        have h5 : r ≤ n := by omega
        nlinarith [sq_nonneg ((r : ℕ) : ℕ)]
      -- Now, bound r from above
      have h6 : r < n + 3 := by
        by_contra h
        push_neg at h
        have h7 : r ≥ n + 3 := by omega
        nlinarith [sq_nonneg ((r : ℕ) : ℕ)]
      -- Now, we know that n < r < n + 3, so r must be n + 1 or n + 2
      have h7 : r = n + 1 ∨ r = n + 2 := by
        omega
      rcases h7 with (h7 | h7)
      · -- r = n + 1
        rw [show r = n + 1 by omega] at hr 
        nlinarith
      · -- r = n + 2
        rw [show r = n + 2 by omega] at hr
        nlinarith
  · -- Assume n = 4, prove IsSquare (n^2 + 5 * n + 13)
    intro h
    rw [h]
    native_decide