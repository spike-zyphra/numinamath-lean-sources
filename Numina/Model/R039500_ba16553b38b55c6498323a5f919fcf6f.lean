import Mathlib

theorem number_theory_608433 :
    IsLeast {p : ℕ | 0 < p ∧ ∃ q : ℕ, 0 < q ∧ 2008 / (2009 : ℚ) < p / (q : ℚ) ∧ p / (q : ℚ) < 2009 / (2010 : ℚ)} 4017 := by
  constructor
  · -- Show that 4017 is in the set.
    constructor
    · norm_num
    · -- We can choose q = 4019.
      use 4019
      norm_num
  · -- Show that 4017 is minimal
    intro p hp
    rcases hp with ⟨hp_pos, q, hq_pos, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : (2008 : ℚ) / (2009 : ℚ) < (p : ℚ) / (q : ℚ) := h1
    have h4 : (p : ℚ) / (q : ℚ) < (2009 : ℚ) / (2010 : ℚ) := h2
    have h5 : (2008 : ℚ) * (q : ℚ) < 2009 * (p : ℚ) := by
      have h6 : (2008 : ℚ) / (2009 : ℚ) < (p : ℚ) / (q : ℚ) := h1
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
      linarith
    have h7 : (2010 : ℚ) * (p : ℚ) < 2009 * (q : ℚ) := by
      have h8 : (p : ℚ) / (q : ℚ) < (2009 : ℚ) / (2010 : ℚ) := h2
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h8
      linarith
    have h8 : (2008 : ℤ) * (q : ℤ) < 2009 * (p : ℤ) := by
      exact_mod_cast h5
    have h9 : (2010 : ℤ) * (p : ℤ) < 2009 * (q : ℤ) := by
      exact_mod_cast h7
    -- Now, we have two integer inequalities:
    -- 1. 2008 * q < 2009 * p
    -- 2. 2010 * p < 2009 * q
    -- We will show that these two inequalities are contradictory when p < 4017
    have h10 : p < 4017 := by
      omega
    omega