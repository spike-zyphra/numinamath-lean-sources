import Mathlib

theorem algebra_4489 {n k : ℕ} (hn : n > 0) (hk : k > 0)
    (h1 : k * n + 14 = 9 * (n - 1) + 6) :
    n = 17 := by
  by_cases h2 : n > 1
  · -- Case n > 1, so n - 1 > 0
    have h7 : k * n + 14 = 9 * (n - 1) + 6 := h1
    have h7' : (k: ℕ) * (n: ℕ) + 17 = 9 * (n : ℕ) := by
      have h6 : k * n + 14 = 9 * (n - 1) + 6 := h1
      have eq2 : 9 * (n - 1) + 6 = 9 * n - 3 := by
        have h7 : n - 1 + 1 = n := by 
          omega 
        have eq3 : 9 * (n - 1) + 6 = 9 * n - 3 := by
          have h8 : n - 1 + 1 = n := h7 
          have h9 : 9 * (n - 1) + 6 = 9 * (n - 1) + 6 := by rfl 
          omega 
        omega 
      omega 
    -- Now n divides 17.
    have h8 : n ≤ 17 := by
      by_contra h
      push_neg at h
      have h10 : k < 9 := by 
        nlinarith [show k * n + 17 = 9 * n by omega, hk]
      interval_cases k <;> try { 
        omega 
      }
    have h9 : n = 17 := by
      interval_cases n <;> 
        omega 
    exact h9
  · -- n ≤ 1, with n > 0 gives n = 1
    have h3 : n = 1 := by
      omega
    rw [h3] at h1
    omega