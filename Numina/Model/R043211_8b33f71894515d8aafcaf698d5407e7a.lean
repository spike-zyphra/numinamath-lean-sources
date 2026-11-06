import Mathlib

theorem number_theory_148587 : ¬∃ (p q : ℤ), 0 < p ∧ 0 < q ∧ p^2 = 2 * q^2 := by
  rintro ⟨p, q, hp, hq, heq⟩
  have h1 : (p : ℚ) ^ 2 = 2 * (q : ℚ) ^ 2 := by
    exact_mod_cast heq
  have h3 : (p / q : ℚ) ^ 2 = (2 : ℚ) := by
    have h4 : (q : ℚ) ≠ 0 := by
      have h4 : 0 < (q : ℚ) := by
        exact_mod_cast hq
      positivity
    field_simp at *
    nlinarith [h1]
  have h4 : IsSquare (2 : ℚ) := by
    use (p / q : ℚ)
    all_goals
      nlinarith [h3]
  have h11 : ¬ IsSquare (2 : ℚ) := by
    native_decide
  contradiction