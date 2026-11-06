import Mathlib

/- The integer value of $a$ that makes the equation $|x|=ax+1$ have both a positive root and a negative root with respect to $x$ is ___          ___. -/
theorem algebra_1694 (a : ℤ) : (∃ x : ℝ, x > 0 ∧ |x| = a * x + 1) ∧ (∃ x : ℝ, x < 0 ∧ |x| = a * x + 1) ↔ a = 0 := by
  constructor
  · -- Assume there exists both positive and negative roots, prove a = 0
    intro h
    rcases h with ⟨h_pos, h_neg⟩
    rcases h_pos with ⟨x1, hx1_pos, h1⟩
    rcases h_neg with ⟨x2, hx2_neg, h2⟩
    
    have h1_pos : x1 = (a : ℝ) * x1 + 1 := by
      rw [abs_of_pos hx1_pos] at h1
      linarith

    have h2_neg : -x2 = (a : ℝ) * x2 + 1 := by
      rw [abs_of_neg hx2_neg] at h2
      linarith
  
    have h3 : (a : ℝ) < 1 := by 
      nlinarith [h1_pos, hx1_pos]

    have h4 : (a : ℝ) > -1 := by 
      nlinarith [h2_neg, hx2_neg]

    have h5 : a < 1 := by 
      by_contra h
      push_neg at h 
      have h6 : (a : ℝ) ≥ (1 : ℝ) := by 
        exact_mod_cast h

      linarith

    have h6 : a > -1 := by
      by_contra h
      push_neg at h 
      have h7 : (a : ℝ) ≤ (-1 : ℝ) := by 
        exact_mod_cast h 
      linarith

    have : a = 0 := by 
      omega

    exact this

  · -- Assume a = 0, prove there exists both positive and negative roots
    intro ha
    have h_pos : ∃ x : ℝ, x > 0 ∧ |x| = (a : ℝ) * x + 1 := by 
      use 1
      constructor 
      · -- Show that 1 > 0
        norm_num
      · -- If a = 0, then |1| = 0 * 1 + 1
        rw [ha]
        norm_num

    have h_neg : ∃ x : ℝ, x < 0 ∧ |x| = (a : ℝ) * x + 1 := by 
      use -1
      constructor 
      · -- Show that -1 < 0
        norm_num
      · -- If a = 0, then |-1| = 0 * (-1) + 1
        rw [ha]
        norm_num

    exact ⟨h_pos, h_neg⟩