import Mathlib

theorem number_theory_60135 :
    IsGreatest {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + (1 / b : ℚ) = 1 / 9 ∧ x = a + b} 100 := by
  constructor
  · -- Show 100 is in the set
    use 10, 90
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num
  · -- Show that it's the greatest
    intro x hx
    rcases hx with ⟨a, b, ha, hb, heq, hx⟩
    have h1 : (a : ℚ) * (b : ℚ) = 9 * ((a : ℚ) + (b : ℚ)) := by
      have h2 : (a : ℚ) > 0 := by exact_mod_cast ha
      have h3 : (b : ℚ) > 0 := by exact_mod_cast hb
      field_simp at heq ⊢
      nlinarith
    have h1' : (a : ℕ) * (b : ℕ) = 9 * ((a : ℕ) + (b : ℕ)) := by
      exact_mod_cast h1
    have h2 : a ≤ 100 := by
      by_contra h
      push_neg at h
      have h3 : b ≤ 9 := by
        nlinarith [h1']
      interval_cases b <;> nlinarith
    have h3 : b ≤ 100 := by
      by_contra h
      push_neg at h
      have h4 : a ≤ 9 := by
        nlinarith [h1']
      interval_cases a <;> nlinarith
    have h4 : a + b ≤ 100 := by
      by_contra h
      push_neg at h
      have h5 : a > 0 := ha
      have h6 : b > 0 := hb
      have h7 : a ≤ 100 := h2
      have  h8 : b ≤ 100 := h3
      interval_cases a <;> omega
    linarith