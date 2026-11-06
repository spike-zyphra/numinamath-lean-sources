import Mathlib

theorem number_theory_95774 (a b c : ℕ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a * b * c = 96) (h₄ : b = 3 * a) (h₅ : c = 4 * a) :
    a = 2 ∧ b = 6 ∧ c = 8 := by
  have eq1 : a * b * c = 96 := h₃
  rw [h₄, h₅] at eq1
  have h6 : a = 2 := by
    have eq2 : a * (3 * a) * (4 * a) = 12 * a^3 := by
      ring
    rw [eq2] at eq1
    have h7 : 12 * a^3 = 96 := by
      linarith
    have h8 : a^3 = 8 := by
      omega
    have h9 : a = 2 := by
      have h10 : a^3 = 8 := h8
      have h11 : a ≤ 2 := by
        by_contra h
        push_neg at h
        have h13 : a ≥ 3 := by omega
        have h14 : a^3 ≥ 27 := by
          have h17 : a ≥ 3 := h13
          have h18 : a^3 ≥ 3^3 := by
            apply Nat.pow_le_pow_of_le_left h17 3
          norm_num at h18 ⊢
          linarith
        have h15 : a^3 < 8 + 1 := by
          omega -- Solving a^3 = 8 and showing a^3 < 9
        all_goals omega
      interval_cases a <;> try { tauto }
    exact h9
  have b_eq : b = 6 := by
    rw [h₄, h6]
    all_goals omega
  have c_eq : c = 8 := by
    rw [h₅, h6]
    all_goals omega
  exact ⟨h6, b_eq, c_eq⟩