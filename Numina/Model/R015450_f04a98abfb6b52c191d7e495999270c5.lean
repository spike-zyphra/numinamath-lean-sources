import Mathlib

theorem number_theory_248777 :
    IsLeast {z | ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ (2010 / 2011 : ℚ) < x / y ∧ x / y < (2011 / 2012 : ℚ) ∧ z = x + y} 8044 := by
  constructor
  · -- Show that 8044 is in the set 
    use 4021, 4023
    norm_num
  · -- Show that it is minimal 
    intro z h
    rcases h with ⟨x, y, hx, hy, h1, h2, h3⟩
    have h4 : (2010 : ℚ) * y < 2011 * x := by
      have h4' : (2010 / 2011 : ℚ) < x / y := h1
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h4'
      linarith
    have h5 : (2012 : ℚ) * x < 2011 * y := by
      have h5' : x / y < (2011 / 2012 : ℚ) := h2
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h5'
      linarith
    have h6 : 2010 * y < 2011 * x := by 
      exact_mod_cast h4
    have h7 : 2012 * x < 2011 * y := by 
      exact_mod_cast h5
    by_contra h
    push_neg at h
    have h8 : x + y < 8044 := by 
      linarith [h3, h]
    have h9 : x ≥ 4021 := by 
      omega
    have h10 : y ≥ 4023 := by 
      omega
    omega