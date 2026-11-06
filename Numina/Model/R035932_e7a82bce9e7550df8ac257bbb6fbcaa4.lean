import Mathlib

theorem number_theory_13786 :
    IsLeast {q : ℕ | ∃ p : ℕ, p > 0 ∧ q > 0 ∧ (72 : ℚ) / 487 < p / q ∧ p / q < (18 : ℚ) / 121} 27 := by 
  constructor
  · -- Show that 27 is in the set
    use 4
    norm_num
  · -- Show that 27 is the smallest such value
    intro q h
    rcases h with ⟨p, hp_pos, hq_pos, h₁, h₂⟩
    by_contra h
    push_neg at h
    have h5 : 72 * (q : ℚ) < 487 * (p : ℚ) := by
      have h3 : (72 : ℚ) / 487 < (p : ℚ) / (q : ℚ) := h₁
      apply (div_lt_div_iff (by norm_num) (by positivity)).mp at h3
      linarith
    have h6 : (121 : ℚ) * (p : ℚ) < 18 * (q : ℚ) := by
      have h4 : (p : ℚ) / (q : ℚ) < (18 : ℚ) / 121 := h₂
      apply (div_lt_div_iff (by positivity) (by norm_num)).mp at h4
      linarith
    have h7 : 72 * q < 487 * p := by
      exact_mod_cast h5
    have h8 : 121 * p < 18 * q := by
      exact_mod_cast h6
    have h9 : q ≤ 26 := by
      omega
    interval_cases q <;> omega