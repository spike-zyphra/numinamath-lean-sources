import Mathlib

theorem number_theory_4004 :
    IsLeast {n : ℕ | ∃ m : ℕ, 0 < m ∧ 0 < n ∧ (560 / 2019 : ℚ) < m / n ∧ m / n < (589 / 2020 : ℚ)} 7 := by
  constructor
  · -- Show 7 is in the set
    use 2
    norm_num
  · -- Show there is no smaller n in the set
    intro n hn
    rcases hn with ⟨m, hm1, hn1, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : n < 7 := by linarith
    have h4 : n < 7 := h3
    have h5 : m > 0 := by linarith
    have h6 : (560 : ℚ) / (2019 : ℚ) < (m : ℚ) / (n : ℚ) := by linarith [h1]
    have h7 : (m : ℚ) / (n : ℚ) < (589 : ℚ) / (2020 : ℚ) := by linarith [h2]
    have h8 : 560 * (n : ℚ) < 2019 * (m : ℚ) := by
      have h8 : (560 : ℚ) / (2019 : ℚ) < (m : ℚ) / (n : ℚ) := h1
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h8
      linarith
    have h9 : 2020 * (m : ℚ) < 589 * (n : ℚ) := by
      have h9 : (m : ℚ) / (n : ℚ) < (589 : ℚ) / (2020 : ℚ) := h2
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h9
      linarith
    have h10 : 560 * n < 2019 * m := by
      exact_mod_cast h8
    have h11 : 2020 * m < 589 * n := by
      exact_mod_cast h9
    interval_cases n <;> try { 
      omega
    }