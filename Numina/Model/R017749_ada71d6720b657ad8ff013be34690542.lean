import Mathlib

theorem number_theory_172965 :
    IsLeast {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = a + b + c ∧ (a / 77 : ℚ) + (b / 91 : ℚ) + (c / 143 : ℚ) = 1} 79 := by
  constructor
  · -- Show 79 is in the set
    use 70, 7, 2
    all_goals norm_num
  · -- Show there is no smaller element in the set
    intro x h
    rcases h with ⟨a, b, c, ha, hb, hc, h1, heq⟩
    by_contra h
    push_neg at h
    have h_eq : (a : ℚ) / 77 + (b : ℚ) / 91 + (c : ℚ) / 143 = 1 := by
      simpa using heq
    have h_eq1 : (13 * (a : ℚ) + 11 * (b : ℚ) + 7 * (c : ℚ) ) = (1001 : ℚ) := by
      have eq : (a : ℚ) / 77 + (b : ℚ) / 91 + (c : ℚ) / 143 = 1 := h_eq
      field_simp at eq ⊢
      nlinarith
    have eq1 : 13 * a + 11 * b + 7 * c = 1001 := by
      exact_mod_cast h_eq1
    have h2 : a + b + c < 79 := by
      omega
    omega