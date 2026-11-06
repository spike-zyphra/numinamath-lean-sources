import Mathlib

theorem number_theory_284735:
IsGreatest {x : ℝ | ∃ a b c : ℕ, 1≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c≤ 9 ∧ x = (100*(a:ℝ)+10*(b:ℝ)+(c:ℝ)) / ((a:ℝ)+(b:ℝ)+(c:ℝ))} 100 := by
  constructor
  · -- Show 100 is in the set
    use 1, 0, 0
    norm_num
  · -- Show there is no greater element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha1, ha2, hb1, hb2, hc1, hc2, h_eq⟩
    have h7 : (100 * (a : ℝ) + 10 * (b : ℝ) + (c : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) ≤ (100 : ℝ) := by
      have h8 : (a : ℝ) + (b : ℝ) + (c : ℝ) > (0 : ℝ) := by
        have ha1' : (a : ℝ) ≥ (1 : ℝ) := by exact_mod_cast ha1
        nlinarith
      apply (div_le_iff₀ h8).mpr
      have ha1' : (a : ℝ) ≥ (1 : ℝ) := by exact_mod_cast ha1
      have hb1' : (b : ℝ) ≥ (0 : ℝ) := by exact_mod_cast hb1
      have hc1' : (c : ℝ) ≥ (0 : ℝ) := by exact_mod_cast hc1
      nlinarith
    linarith [h_eq, h7]