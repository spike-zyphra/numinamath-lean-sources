import Mathlib

theorem number_theory_1101 {n m : ℕ} (hn : n > 0) (hm : m > 0) (h1 : m * n + 5 = 8 * n)
    (h2 : m * (n + 1) = 56 * n + 8) :
    n = 6 ∧ m = 11 := by
  -- We need to prove n ≤ 8 by contradiction
  have h3 : n ≤ 8 := by
    by_contra h
    push_neg at h
    have h4 : m * n + 5 = 8 * n := h1
    have h5 : m * n < 8 * n := by 
      omega
    have h6 : m < 8 := by
      apply (mul_lt_mul_iff_of_pos_right hn).mp at h5
      omega
    -- Now, we need to derive a contradiction from h6 and h2
    have h2' : m * (n + 1) = 56 * n + 8 := h2
    have h8 : m * (n + 1) ≤ 7 * (n + 1) := by
      have h9 : m ≤ 7 := by omega
      nlinarith [h9, show n + 1 > 0 by omega]
    -- The previous steps lead to the following contradiction
    omega
  -- Now n ≤ 8, so we can check each case
  interval_cases n <;> omega