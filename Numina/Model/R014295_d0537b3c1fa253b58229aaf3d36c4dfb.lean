import Mathlib

theorem inequalities_5966 (c : ℝ) (a d : ℝ) (hc : c > 0) (ha : 0 < a ∧ a < c) (hd : 0 < d ∧ d < c) :
    0 < (a + d) / (1 + a * d / c ^ 2) ∧ (a + d) / (1 + a * d / c ^ 2) < c := by 
  rcases ha with ⟨ha_pos, ha_lt_c⟩
  rcases hd with ⟨hd_pos, hd_lt_c⟩
  have h1 : 0 < (a + d : ℝ) := by
    linarith
  have h2 : 0 < (1 + a * d / c ^ 2 : ℝ) := by
    have hc2_pos : 0 < c ^ 2 := by
      nlinarith
    have had_pos : 0 < a * d := by
      nlinarith
    have h3 : 0 < (a * d / c ^ 2 : ℝ) := by
      apply div_pos
      all_goals nlinarith
    nlinarith
  have h3 : 0 < (a + d) / (1 + a * d / c ^ 2 : ℝ) := by
    apply div_pos
    all_goals linarith
  have h4 : (a + d) / (1 + a * d / c ^ 2 : ℝ) < c := by
    have h5 : 0 < (1 + a * d / c ^ 2 : ℝ) := h2
    apply (div_lt_iff₀ h5).mpr
    have hc2_pos : 0 < c ^ 2 := by
      nlinarith
    have h7 : (a + d) * c < c ^ 2 + a * d := by
      have ha1 : a < c := ha_lt_c
      have hd1 : d < c := hd_lt_c
      have h8 : (a - c) * (c - d) < 0 := by
        have h9 : a - c < 0 := by linarith
        have h10 : c - d > 0 := by linarith
        nlinarith
      nlinarith
    have h7' : (a + d) < c * (1 + a * d / c ^ 2) := by
      have h8 : c * (1 + a * d / c ^ 2) = (c ^ 2 + a * d) / c := by
        field_simp
        <;> nlinarith
      rw [h8] at *
      apply (lt_div_iff₀ (by linarith)).mpr
      nlinarith
    linarith
  constructor
  · exact h3
  · exact h4