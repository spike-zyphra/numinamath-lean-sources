import Mathlib

  theorem inequalities_254760 :
    {(a, b) : ℕ × ℕ | 0 < a ∧ 0 < b ∧ (a / 5 : ℝ) < 1 ∧ (b / 7 : ℝ) < 1 ∧
    1 < (a / 5 : ℝ) + (b / 7 : ℝ) ∧ (a / 5 : ℝ) + (b / 7 : ℝ) < 2} = {(1, 6), (2, 5), (2, 6), (3, 3), (3, 4), (3, 5), (3, 6), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6)} := by
  ext ⟨a, b⟩
  simp 
  constructor 
  · -- Assume ⟨a, b⟩ is in the set, prove it's one of the pairs 
    rintro ⟨ha, hb, h1, h2, h3, h4⟩ 
    have h11 : a < 5 := by
      by_contra h 
      push_neg at h 
      have h12 : a ≥ 5 := by omega 
      have h12' : (a : ℝ) ≥ (5 : ℝ) := by 
        exact_mod_cast h12 
      nlinarith 
    have h22 : b < 7 := by 
      by_contra h 
      push_neg at h 
      have h23 : b ≥ 7 := by omega 
      have h23' : (b : ℝ) ≥ (7 : ℝ) := by 
        exact_mod_cast h23 
      nlinarith 
    have h3' : (7 * (a : ℝ) + 5 * (b : ℝ)) > (35 : ℝ) := by 
      nlinarith 
    have h4' : (7 * (a : ℝ) + 5 * (b : ℝ)) < (70 : ℝ) := by 
      nlinarith 
    have h5 : 7 * a + 5 * b > 35 := by 
      exact_mod_cast h3' 
    have h6 : 7 * a + 5 * b < 70 := by 
      exact_mod_cast h4' 
    interval_cases a <;> interval_cases b 
    <;> norm_num at h1 h2 h3 h4 h5 h6 ⊢ 
    <;> tauto 
  · -- Show the right side is in the set
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num