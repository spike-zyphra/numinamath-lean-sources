import Mathlib

theorem inequalities_315661 :
    IsLeast {n : ℕ | ∃ k : ℕ, 0 < n ∧ 0 < k ∧ 8 / 15 < (n : ℝ) / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13} 15 := by
  constructor
  · -- Show 15 is in the set
    use 13
    norm_num
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨k, hn_pos, hk_pos, h1, h2⟩
    by_contra h
    push_neg at h
    have h4 : n < 15 := by linarith
    have h5 : (8 : ℝ) * (n + (k : ℝ)) < 15 * (n : ℝ) := by
      have h5 : (8 / 15 : ℝ) < (n : ℝ) / (n + k) := h1
      apply (lt_div_iff₀ (by positivity)).mp at h5
      nlinarith
    have h6 : (13 * (n : ℝ) : ℝ) < 7 * (n + (k : ℝ)) := by
      have h7 : (n : ℝ) / (n + k) < (7 / 13 : ℝ) := h2
      apply (div_lt_iff₀ (by positivity)).mp at h7
      nlinarith
    -- Convert the inequalities to integer form
    have h9 : (8 : ℝ) * ((n + k : ℝ) ) < (15 * (n : ℝ)) := by
      nlinarith
    have h10 : (13 * (n : ℝ) : ℝ) < (7 * (n + (k : ℝ))) := by
      nlinarith
    have h5k : (8) * (n + k) < (15 * n) := by
      exact_mod_cast h9
    have h6k : (13 * n) < (7 * (n + k)) := by
      exact_mod_cast h10
    interval_cases n <;> omega