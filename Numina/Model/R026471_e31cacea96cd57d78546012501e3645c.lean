import Mathlib

theorem number_theory_96501 : IsLeast {n : ℕ | n ≥ 26 ∧ ∃ k : ℤ, ((123456789 : ℝ) / (2^26 * 5^4)) = k / 10^n} 26 := by
  constructor
  · -- Show 26 is in the set.
    constructor
    · norm_num
    · -- Show that there exists an integer k such that 123456789/(2^26*5^4) = k/10^26.
      use (123456789 * 5 ^ 22)
      field_simp
      <;> norm_num
      <;> linarith
  · -- Show that 26 is the least.
    intro n hn
    rcases hn with ⟨hn1, k, hk⟩
    by_contra h
    push_neg at h
    -- Now we have a contradiction.
    have eq1 : (123456789 : ℝ) / (2^26 * 5^4) = (k : ℝ) / (10 : ℝ) ^ n := by
      simpa using hk
    have eq2 : (123456789 : ℝ) * (10 : ℝ) ^ n = (k : ℝ) * (2^26 * 5^4) := by
      have h1 : (k : ℝ) / (10 : ℝ) ^ n = (123456789 : ℝ) / (2^26 * 5^4) := by linarith [eq1]
      field_simp at h1 ⊢
      <;> ring_nf at h1 ⊢
      <;> nlinarith
    have eq3 : (123456789 : ℤ) * (10 : ℤ) ^ n = (k : ℤ) * (2^26 * 5^4) := by
      exact_mod_cast eq2
    -- Now derive a contradiction for the value of n less than 26.
    interval_cases n <;> norm_num at eq3 <;> 
      try { 
        omega 
      }
      <;> 
        try { 
          exfalso 
          <;> 
            try { 
              omega 
            } 
        }
  all_goals linarith