import Mathlib

theorem number_theory_5515 :
    IsLeast {k | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m < n ∧ (315 / 1000 : ℝ) < (m / n : ℝ) ∧ (m / n : ℝ) < (316 / 1000 : ℝ) ∧ k = m + n} 25 := by
  constructor
  · -- Show that 25 is in the set by finding m, n.
    use 6, 19
    constructor
    · norm_num  -- m > 0
    constructor
    · norm_num  -- n > 0
    constructor
    · norm_num  -- m < n
    constructor
    · norm_num  -- 0.315 < 6/19
    constructor
    · norm_num  -- 6/19 < 0.316
    · norm_num  -- k = 25
  · -- Show that 25 is the least element in the set
    intro k hk
    rcases hk with ⟨m, n, hm_pos, hn_pos, h1, h4, h5, hk⟩
    by_contra h
    push_neg at h
    have h2 : m + n < 25 := by
      omega
    have h6 : m ≤ 23 := by
      omega
    have h7 : n ≤ 24 := by
      omega
    have h1' : (315 : ℝ) / 1000 < (m : ℝ) / (n : ℝ) := by
      exact_mod_cast h4
    have h2' : (m : ℝ) / (n : ℝ) < (316 : ℝ) / 1000 := by
      exact_mod_cast h5
    have h3 : 315 * (n : ℝ) < 1000 * (m : ℝ) := by
      have h7 : (n : ℝ) > 0 := by
        exact_mod_cast show n > 0 by linarith
      have h8 : (315 : ℝ) / 1000 < (m : ℝ) / (n : ℝ) := by
        exact_mod_cast h4
      have h9 : 315 * (n : ℝ) < 1000 * (m : ℝ) := by
        have h10 : (315 : ℝ) / 1000 < (m : ℝ) / (n : ℝ) := h8
        have h11 : (n : ℝ) > 0 := by exact_mod_cast show n > 0 by linarith
        have h12 : (315 : ℝ) * (n : ℝ) < 1000 * (m : ℝ) := by
          have h13 : (315 / 1000 : ℝ) < (m / (n : ℝ)) := h10
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h13
          nlinarith
        linarith
      linarith
    have h4' : 1000 * (m : ℝ) < 316 * (n : ℝ) := by
      have h7 : (n : ℝ) > 0 := by
        exact_mod_cast show n > 0 by linarith
      have h8 : (m : ℝ) / (n : ℝ) < (316 : ℝ) / 1000 := by
        exact_mod_cast h5
      have h9 : 1000 * (m : ℝ) < 316 * (n : ℝ) := by
        have h10 : (m : ℝ) / (n : ℝ) < (316 : ℝ) / 1000 := h8
        have h11 : (n : ℝ) > 0 := by exact_mod_cast show n > 0 by linarith
        have h12 : 1000 * (m : ℝ) < 316 * (n : ℝ) := by
          have h13 : (m / (n : ℝ)) < (316 / 1000 : ℝ) := h10
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h13
          nlinarith
        linarith
      linarith
    have h5 : 315 * n < 1000 * m := by
      exact_mod_cast h3
    have h6' : 1000 * m < 316 * n := by
      exact_mod_cast h4'
    interval_cases n <;> interval_cases m
    <;> norm_num at h5 h6' <;> omega