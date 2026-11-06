import Mathlib

theorem number_theory_309838 : IsLeast {x : ℤ | ∃ a b c : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x = (a:ℝ) * b * c / (a + b + c)} 1 := by
  constructor 
  · -- Show 1 is in the set
    use 2, 1, 3 
    norm_num 
    all_goals norm_num 
  · -- Show 1 is the least 
    intro x hx 
    rcases hx with ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hx⟩ 
    by_contra h 
    push_neg at h 
    have h1 : x < 1 := by linarith 
    have h2 : x ≤ 0 := by omega 
    have h3 : (a : ℝ) * b * c / (a + b + c) = (x : ℝ) := by 
      linarith [hx] 
    have h4 : (a * b * c : ℝ) = x * (a + b + c : ℝ) := by 
      have h5 : (a : ℝ) * b * c / (a + b + c) = (x : ℝ) := by
        linarith [hx]
      have h6 : (a : ℝ) * b * c / (a + b + c) = (a * b * c : ℝ) / (a + b + c : ℝ) := by 
        ring 
      rw [h6] at h5
      have h7 : (a : ℝ) + (b : ℝ) + (c : ℝ) > (0 : ℝ) := by 
        have ha1 : (a : ℝ) > (0 : ℝ) := by 
          exact_mod_cast ha 
        have hb1 : (b : ℝ) > (0 : ℝ) := by 
          exact_mod_cast hb 
        have hc1 : (c : ℝ) > (0 : ℝ) := by 
          exact_mod_cast hc 
        linarith 
      have h8 : (a + b + c : ℝ) ≠ (0 : ℝ) := by 
        linarith 
      field_simp [h8] at h5 ⊢ 
      all_goals nlinarith 
    have h5 : a * b * c = x * (a + b + c) := by 
      exact_mod_cast h4 
    have h6 : x = 0 := by 
      nlinarith [show 0 < a + b + c by linarith, 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      show x ≤ 0 by omega, 
      sq_pos_of_ne_zero (show (a - b) ≠ 0 by 
        intro h'
        apply hab 
        omega 
      ), 
      sq_pos_of_ne_zero (show (a - c) ≠ 0 by 
        intro h'
        apply hac 
        omega 
      ), 
      sq_pos_of_ne_zero (show (b - c) ≠ 0 by 
        intro h'
        apply hbc 
        omega 
      )
      ] 
    have h8 : a * b * c = 0 := by 
      norm_num [h5, h6] at *
      all_goals nlinarith 
    cases' (mul_eq_zero.1 h8) with h9 h10 
    cases' (mul_eq_zero.1 h9) with h11 h12 
    · -- `a = 0` 
      exfalso 
      linarith 
    · -- `b = 0` 
      exfalso 
      linarith 
    · -- `c = 0` 
      exfalso 
      linarith