import Mathlib

theorem inequalities_3240 (x : ℤ) (hx : x ≠ -3) :
    (x + 5 + 1 / (x + 3 : ℝ) ≥ 1 / (x + 3) - 4 - 2 * x) ↔ x > -3 := by
  constructor
  · -- Assume the inequality holds, prove x > -3
    intro h
    have h1 : (x : ℝ) ≠ -3 := by
      exact_mod_cast hx
    have h2 : (x + 5 : ℝ) + (1 / (x + 3 : ℝ)) ≥ (1 / (x + 3 : ℝ) ) - 4 - (2 * (x : ℝ) ) := by
      have h2' : (x + 5 + 1 / (x + 3 : ℝ) ≥ 1 / (x + 3) - 4 - 2 * x) := h
      exact_mod_cast h2'
    have h3 : (x + 5 : ℝ) ≥ -4 - (2 * (x : ℝ) ) := by
      have h4 : (x + 3 : ℝ) ≠ 0 := by
        intro h5
        have : (x : ℝ) = -3 := by
          linarith
        contradiction
      have h5 : (x + 5 : ℝ) + (1 / (x + 3 : ℝ)) - (1 / (x + 3 : ℝ) ) ≥ ( (1 / (x + 3 : ℝ) ) - 4 - (2 * (x : ℝ) ) ) - (1 / (x + 3 : ℝ) ) := by linarith [h2]
      have h6 : (x + 5 : ℝ) + (1 / (x + 3 : ℝ) ) - (1 / (x + 3 : ℝ) ) = (x + 5 : ℝ) := by
        ring
      have h7 : ( (1 / (x + 3 : ℝ) ) - 4 - (2 * (x : ℝ) ) ) - (1 / (x + 3 : ℝ) ) = -4 - (2 * (x : ℝ) ) := by
        ring
      rw [h6, h7] at h5
      linarith
    have h4 : x ≥ -3 := by
      by_contra h4
      push_neg at h4
      have h5 : x ≤ -4 := by 
        omega
      have h6 : (x : ℝ) ≤ (-4 : ℝ) := by 
        exact_mod_cast h5
      nlinarith 
    have h5 : x > -3 := by
      by_contra h5
      push_neg at h5 
      have h6 : x ≤ -3 := by
        omega 
      have h7 : x = -3 := by 
        omega 
      contradiction
    exact h5
  · -- Assume x > -3, prove the inequality
    intro h 
    have h1 : x ≥ -2 := by 
      omega
    have h2 : (x : ℝ) ≥ (-2 : ℝ) := by 
      exact_mod_cast h1 
    have h3 : (x + 5 : ℝ) ≥ -4 - (2 * (x : ℝ) ) := by
      linarith 
    have h4 : (x + 5 : ℝ) + (1 / (x + 3 : ℝ)) ≥ (1 / (x + 3 : ℝ) ) - 4 - (2 * (x : ℝ) ) := by
      have h4 : (x + 3 : ℝ) ≠ 0 := by 
        by_contra h6
        have : (x : ℝ) = -3 := by 
          linarith 
        have h8 : x = -3 := by 
          exact_mod_cast this 
        contradiction 
      have h6 : (x + 5 : ℝ) ≥ -4 - (2 * (x : ℝ) ) := h3 
      have h5 : (x + 5 : ℝ) + (1 / (x + 3 : ℝ)) - (1 / (x + 3 : ℝ) ) ≥ ( (1 / (x + 3 : ℝ) ) - 4 - (2 * (x : ℝ) ) ) - (1 / (x + 3 : ℝ) ) := by linarith [h6]
      have h7 : (x + 5 : ℝ) + (1 / (x + 3 : ℝ) ) - (1 / (x + 3 : ℝ) ) = (x + 5 : ℝ) := by 
        ring 
      have h8 : ( (1 / (x + 3 : ℝ) ) - 4 - (2 * (x : ℝ) ) ) - (1 / (x + 3 : ℝ) ) = ( -4 - (2 * (x : ℝ) ) ) := by 
        ring 
      rw [h7, h8] at h5 
      linarith 
    exact_mod_cast h4