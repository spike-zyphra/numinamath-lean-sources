import Mathlib

  theorem number_theory_6881 :
    IsLeast {x : ℝ | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * 15.6 = x ∧ b * 16.8 = x ∧ c * 18.2 = x} (218.4) := by
    constructor
    · -- Show that 218.4 is in the set
      use 14, 13, 12
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
    · -- Show that 218.4 is the minimum
      intro x hx
      rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩
      have h4 : x ≥ (218.4 : ℝ) := by
        have eq1 : (a : ℝ) * 15.6 = (b : ℝ) * 16.8 := by
          linarith
        have eq2 : (a : ℝ) * 15.6 = (c : ℝ) * 18.2 := by
          linarith
        have eq3 : (a : ℝ) * 156 = (b : ℝ) * 168 := by 
          have h := eq1
          ring_nf at h ⊢
          linarith
        have eq4 : (a : ℝ) * 156 = (c : ℝ) * 182 := by 
          have h := eq2
          ring_nf at h ⊢
          linarith
        have eq7' : a * 78 = b * 84 := by 
          have h7 : (a : ℝ) * 78 = (b : ℝ) * 84 := by
            have h10 : (a : ℝ) * 15.6 = (b : ℝ) * 16.8 := by
              linarith
            ring_nf at h10 ⊢
            linarith
          exact_mod_cast h7
        have eq8' : a * 78 = c * 91 := by 
          have h8 : (a : ℝ) * 78 = (c : ℝ) * 91 := by
            have h13 : (a : ℝ) * 15.6 = (c : ℝ) * 18.2 := by
              linarith
            ring_nf at h13 ⊢
            linarith
          exact_mod_cast h8
        have h15 : a ≥ 14 := by 
          omega
        have ha1 : (a : ℝ) ≥ (14 : ℝ) := by
          exact_mod_cast h15
        nlinarith
      linarith