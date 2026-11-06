import Mathlib

theorem number_theory_4823 :
  IsLeast {x | ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ 0.315 < (m / n : ℝ) ∧ (m / n : ℝ) < 0.316 ∧ x = m + n} 25 := by
  constructor
  · -- Show 25 is in the set
    use 6, 19
    norm_num
    all_goals norm_num
  · -- Show that 25 is the smallest
    intro x hx
    rcases hx with ⟨m, n, hm, hn, h1, h2, hx⟩
    by_contra h
    push_neg at h
    have h3 : m + n < (25 : ℤ) := by linarith [hx, h]
    have h4 : m > 0 := by linarith
    have h5 : n > 0 := by linarith
    have h6 : (63 : ℝ) * (n : ℝ) < (200 : ℝ) * (m : ℝ) := by
      have h9 : (m : ℝ) / (n : ℝ) > (0.315 : ℝ) := by linarith [h1]
      have h10 : (m : ℝ) / (n : ℝ) > (63 / 200 : ℝ) := by
        norm_num at h9 ⊢
        linarith
      have h12 : (n : ℝ) > 0 := by positivity
      have h11 : (200 : ℝ) * (m : ℝ) > (63 : ℝ) * (n : ℝ) := by
        have h12 : (n : ℝ) > 0 := by positivity
        apply (lt_div_iff₀ (by positivity)).mp at h10
        nlinarith
      nlinarith
    have h7 : (250 : ℝ) * (m : ℝ) < (79 : ℝ) * (n : ℝ) := by
      have h13 : (m : ℝ) / (n : ℝ) < (0.316 : ℝ) := by linarith [h2]
      have h14 : (m : ℝ) / (n : ℝ) < (79 / 250 : ℝ) := by
        norm_num at h13 ⊢
        linarith
      have h16 : (n : ℝ) > 0 := by positivity
      have h15 : (250 : ℝ) * (m : ℝ) < (79 : ℝ) * (n : ℝ) := by
        have h16 : (n : ℝ) > 0 := by positivity
        apply (div_lt_iff₀ (by positivity)).mp at h14
        nlinarith
      nlinarith
    have h8 : 63 * n < 200 * m := by
      by_contra h
      push_neg at h
      have : (63 * (n : ℝ) ) ≥ (200 * (m : ℝ)) := by
        have hn1 : (63 * n : ℝ) ≥ (200 * m : ℝ) := by
          exact_mod_cast h
        nlinarith
      linarith
    have h9 : 250 * m < 79 * n := by
      by_contra h
      push_neg at h
      have : (250 * (m : ℝ) ) ≥ (79 * (n : ℝ)) := by
        have hn1 : (250 * m : ℝ) ≥ (79 * n : ℝ) := by
          exact_mod_cast h
        nlinarith
      linarith
    have h10 : m ≤ 23 := by 
      omega
    have h11 : n ≤ 23 := by 
      omega
    interval_cases m <;> 
      interval_cases n <;> norm_num at h8 h9 h3 h4 h5 hx <;> all_goals omega