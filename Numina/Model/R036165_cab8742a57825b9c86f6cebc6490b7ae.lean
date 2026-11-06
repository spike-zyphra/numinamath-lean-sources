import Mathlib

theorem number_theory_154702 :
    IsLeast {p : ℕ | ∃ q : ℕ, 0 < p ∧ 0 < q ∧ (2008 / 2009 : ℚ) < (p / q : ℚ) ∧ (p / q : ℚ) < (2009 / 2010 : ℚ)} 4017 := by
  constructor
  · -- Show 4017 is in the set
    use 4019
    norm_num
  · -- Show no smaller p is in the set
    intro p hp
    rcases hp with ⟨q, hp_pos, hq_pos, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : (2008 : ℚ) / (2009 : ℚ) < (p : ℚ) / (q : ℚ) := h1
    have h4 : (p : ℚ) / (q : ℚ) < (2009 : ℚ) / (2010 : ℚ) := h2
    have h5 : 2008 * (q : ℚ) < 2009 * (p : ℚ) := by
      have h3' : (2008 : ℚ) / (2009 : ℚ) < (p : ℚ) / (q : ℚ) := h1
      have h6 : (q : ℚ) > 0 := by exact_mod_cast (show 0 < q by linarith)
      have h7 : (2009 : ℚ) > 0 := by norm_num
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h3'
      linarith
    have h5' : 2008 * q < 2009 * p := by
      exact_mod_cast h5
    have h8 : (p : ℚ) * (2010 : ℚ) < 2009 * (q : ℚ) := by
      have h4' : (p : ℚ) / (q : ℚ) < (2009 : ℚ) / (2010 : ℚ) := h2
      have h6 : (q : ℚ) > 0 := by exact_mod_cast (show 0 < q by linarith)
      have h7 : (2010 : ℚ) > 0 := by norm_num
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h4'
      linarith
    have h8' : p * 2010 < 2009 * q := by
      exact_mod_cast h8
    have h9 : p ≤ 4016 := by
      omega
    omega