import Mathlib

theorem number_theory_686 :
    IsLeast {y : ℕ | ∃ x : ℕ, x > 0 ∧ y > 0 ∧ (2011 / 2012 : ℝ) < (x / y : ℝ) ∧ (x / y : ℝ) < (2012 / 2013 : ℝ)} 4025 := by
  constructor 
  · -- Show 4025 is indeed in the set. 
    use 4023 
    norm_num 
  · -- Show there is no smaller y in the set. 
    intro y hy 
    rcases hy with ⟨x, hx1, hy1, h1, h2⟩ 
    by_contra h 
    push_neg at h 
    have h3 : (2011 : ℝ) / (2012 : ℝ) < (x / y : ℝ) := by 
      linarith 
    have h4 : (x / y : ℝ) < (2012 / 2013 : ℝ) := by 
      linarith 
    -- Clear denominators and convert to linear constraints 
    have h5 : (2011 * (y : ℝ) : ℝ) < (2012 * (x : ℝ) : ℝ) := by 
      have h6 : (2011 / 2012 : ℝ) < (x / y : ℝ) := h3 
      have h7 : (0 : ℝ) < (y : ℝ) := by
        exact_mod_cast show (0 : ℕ) < y by linarith
      have h8 : (0 : ℝ) < (2012 : ℝ) := by norm_num 
      have h9 : (2011 * (y : ℝ) < 2012 * (x : ℝ)) := by
        have h9 : (2011 / 2012 : ℝ) < (x / y : ℝ) := h3 
        apply (div_lt_div_iff (by norm_num) (by positivity)).mp at h9 
        linarith
      linarith 
    have h6 : (2013 * (x : ℝ) : ℝ) < (2012 * (y : ℝ) : ℝ) := by 
      have h7 : (x / y : ℝ) < (2012 / 2013 : ℝ) := h4 
      have h8 : (0 : ℝ) < (y : ℝ) := by 
        exact_mod_cast show (0 : ℕ) < y by linarith 
      have h9 : (0 : ℝ) < (2013 : ℝ) := by norm_num 
      have h10 : (2013 * (x : ℝ) < 2012 * (y : ℝ)) := by
        have h9 : (x / y : ℝ) < (2012 / 2013 : ℝ) := h4 
        apply (div_lt_div_iff (by positivity) (by positivity)).mp at h9 
        linarith
      linarith 
    -- Convert real constraints to natural numbers without denominators 
    have h7 : 2011 * y < 2012 * x := by 
      have h20 : (2011 * (y : ℝ) : ℝ) < (2012 * (x : ℝ) : ℝ) := h5 
      exact_mod_cast h20 
    have h8 : 2013 * x < 2012 * y := by 
      have h20 : (2013 * (x : ℝ) : ℝ) < (2012 * (y : ℝ) : ℝ) := h6 
      exact_mod_cast h20 
    -- Now with the inequalities clear, derive y >= 4025
    have h9 : y ≥ 4025 := by 
      omega 
    -- This is a contradiction with our assumption y < 4025
    omega