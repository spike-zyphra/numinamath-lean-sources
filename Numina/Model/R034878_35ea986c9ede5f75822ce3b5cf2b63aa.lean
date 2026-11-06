import Mathlib
theorem number_theory_165651 : 
    { (a, b) : ℕ × ℕ | 90 < a + b ∧ a + b < 100 ∧ 0.9 < (a : ℝ) / (b : ℝ) ∧ (a : ℝ) / (b : ℝ) < 0.91 } = 
    { (46, 51), (47, 52) } := by
  ext ⟨a, b⟩
  simp
  constructor
  · -- Forward implication: If (a, b) is in the left side, then it's in the right side
    rintro ⟨h1, h2, h3, h4⟩
    have h5 : (a : ℝ) / (b : ℝ) > (0.9 : ℝ) := by
      linarith
    have h6 : (a : ℝ) / (b : ℝ) < (0.91 : ℝ) := by
      linarith
    have hb : (b : ℝ) > (0 : ℝ) := by
      by_contra h
      push_neg at h
      have h7 : (b : ℝ) = (0 : ℝ) := by
        nlinarith
      have h8 : (b : ℝ) = (0 : ℝ) := by
        linarith
      rw [h8] at h3 h4 h5 h6
      norm_num at h3 h4 h5 h6
      all_goals linarith
    have h7 : 9 * b < 10 * a := by
      have h8 : (a : ℝ) / (b : ℝ) > (0.9 : ℝ) := by
        linarith
      have h9 : (a : ℝ) > (0.9 : ℝ) * (b : ℝ) := by
        apply (lt_div_iff' (by nlinarith)).mp at h8
        linarith
        all_goals nlinarith
        all_goals nlinarith
      have h10 : (a : ℝ) > (0.9 : ℝ) * (b : ℝ) := by
        linarith
      have h11 : (9 * (b : ℝ) : ℝ) < (10 * (a : ℝ) : ℝ) := by
        nlinarith
      exact_mod_cast h11
    have h7 : a ≤ 99 := by
      linarith
    have h8 : 100 * a < 91 * b := by
      have h9 : (a : ℝ) / (b : ℝ) < (0.91 : ℝ) := by
        linarith
      have h10 : (a : ℝ) < (0.91 : ℝ) * (b : ℝ) := by
        apply (div_lt_iff (by nlinarith)).mp at h9
        linarith
      have h11 : (a : ℝ) < (0.91 : ℝ) * (b : ℝ) := by
        linarith
      have h12 : (100 * (a : ℝ) : ℝ) < (91 * (b : ℝ) : ℝ) := by
        nlinarith
      exact_mod_cast h12
    interval_cases a <;> try { 
      omega 
    } <;> try { 
      all_goals
      have h13 : b ≤ 99 := by
        omega
      interval_cases b <;> norm_num at h3 h4 h5 h6 h7 h8 ⊢ <;> try { 
        omega 
      } <;> try { 
        tauto 
      } 
      <;> omega
    }
  · -- Backward implication: If (a, b) is in the right side, then it's in the left side
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- For (46, 51)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- For (47, 52)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num