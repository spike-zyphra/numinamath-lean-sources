import Mathlib

theorem number_theory_307661 :
    IsLeast {r : ℝ | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m ≤ 1996 ∧ r = 2 - m / n ∧ r > 0} (1 / 998) := by
  constructor
  · -- Show 1/998 is in the set
    use 1995, 998
    norm_num
  · -- Show 1/998 is minimal
    intro r hr
    rcases hr with ⟨m, n, hm, hn, hm1, hr_eq, h1⟩
    by_contra h
    push_neg at h
    have h2 : (2 : ℝ) - (m : ℝ) / (n : ℝ) < (1 / 998 : ℝ) := by linarith [hr_eq, h]
    have h3 : m * 998 > 1995 * n := by 
      by_contra h4
      push_neg at h4 
      have h4' : (m : ℝ) * (998 : ℝ) ≤ (1995 : ℝ) * (n : ℝ) := by
        exact_mod_cast h4
      have h5 : (2 : ℝ) - (m : ℝ) / (n : ℝ) ≥ (1 / 998 : ℝ) := by 
        have h6 : (m : ℝ) / (n : ℝ) ≤ (1995 : ℝ) / (998 : ℝ) := by 
          have hn' : (n : ℝ) > 0 := by exact_mod_cast show (n : ℕ) > 0 by linarith
          apply (div_le_div_iff (by positivity) (by positivity)).mpr 
          nlinarith [h4']
        linarith [h6]
      linarith [h5, h2]
    have h4 : m * 998 > 1995 * n := h3
    have h6 : (m : ℝ) < (2 * (n : ℝ) ) := by 
      have hr1 : (2 : ℝ) - (m : ℝ) / (n : ℝ) > 0 := by 
        linarith [hr_eq, h1]
      have ht1 : (m : ℝ) / (n : ℝ) < (2 : ℝ) := by 
        nlinarith [hr1]
      have ht2 : (m : ℝ) < (2 * (n : ℝ)) := by
        have hn1 : (n : ℝ) > 0 := by 
          exact_mod_cast show (n : ℕ) > 0 by linarith
        apply (div_lt_iff' (by linarith)).mp at ht1
        linarith
      linarith 
    have h7 : m < 2 * n := by 
      have h6' : (m : ℝ) < (2 * (n : ℝ) ) := h6 
      have h8 : (m : ℝ) < (2 * (n : ℝ) ) := by linarith 
      norm_cast at h8 ⊢
      all_goals omega
    have h8 : m ≤ 1996 := hm1
    by_cases h9 : n < 998
    · -- If n < 998, then n ≤ 997
      have h10 : n ≤ 997 := by omega
      exfalso
      -- need further proof here. Let's jump into nlinarith with all facts.
      nlinarith
    · -- n ≥ 998
      have h11 : n ≥ 998 := by omega
      have h12 : n ≤ 998 := by
        nlinarith [show m ≤ 1996 by omega, h4, h7]
      have h13 : n = 998 := by linarith
      -- m * 998 > 1995 * 998
      have h14 : m > 1995 := by 
        have ht1 : m * 998 > 1995 * 998 := by 
          rw [h13] at h4
          all_goals omega 
        nlinarith 
      have h15 : m = 1996 := by 
        omega 
      rw [h15, h13] at hr_eq 
      norm_num at hr_eq
      linarith