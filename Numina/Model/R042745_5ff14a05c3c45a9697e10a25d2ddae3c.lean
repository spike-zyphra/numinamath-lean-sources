import Mathlib


theorem number_theory_44406 (d : ℕ) (hd : d > 0) : (∃ a b c : ℚ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ d = (1/2) * a * b) ↔ (∃ x y z : ℚ, x^2 - y^2 = d ∧ y^2 - z^2 = d) := by
  constructor
  · -- Assume ∃ a b c : ℚ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ d = (1/2) * a * b, prove ∃ x y z : ℚ, x^2 - y^2 = d ∧ y^2 - z^2 = d
    rintro ⟨a, b, c, ha, hb, hc, h1, heq⟩
    use (a + b) / 2, c / 2, (a - b) / 2
    constructor
    · -- Show x^2 - y^2 = d
      have heq' : (d : ℚ) = (1 / 2 : ℚ) * a * b := by exact_mod_cast heq
      nlinarith
    · -- Show y^2 - z^2 = d
      have heq' : (d : ℚ) = (1 / 2 : ℚ) * a * b := by exact_mod_cast heq
      nlinarith
  · -- Assume ∃ x y z : ℚ, x^2 - y^2 = d ∧ y^2 - z^2 = d, prove ∃ a b c : ℚ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ d = (1/2) * a * b
    rintro ⟨x, y, z, h_eq1, h_eq2⟩
    have h10 : (x + z) * (x - z) > 0 := by
      have h11 : (x + z) * (x - z) = 2 * (d : ℚ) := by
        nlinarith
      have h12 : (d : ℚ) > 0 := by exact_mod_cast (show (d : ℚ) > 0 by exact_mod_cast (show d > 0 by linarith))
      nlinarith
    have h13 : (x + z) > 0 ∧ (x - z) > 0 ∨ (x + z) < 0 ∧ (x - z) < 0 := by
      apply Or.elim (mul_pos_iff.mp h10)
      · -- Case where (x + z) > 0 and (x - z) > 0
        intro h
        exact Or.inl ⟨h.1, h.2⟩
      · -- Case where (x + z) < 0 and (x - z) < 0
        intro h
        exact Or.inr ⟨by linarith, by linarith⟩
    rcases h13 with h13 | h13
    · -- Case where (x + z) > 0 and (x - z) > 0
      have h100 : (y) > 0 ∨ (y) < 0 := by
        by_contra h
        push_neg at h
        have : y = 0 := by linarith
        nlinarith
      rcases h100 with h100 | h100
      · -- Assume y > 0
        use x + z, x - z, 2 * y
        constructor
        · -- Show a > 0
          nlinarith
        constructor
        · -- Show b > 0
          nlinarith
        constructor
        · -- Show c > 0
          nlinarith
        constructor
        · -- Show a^2 + b^2 = c^2
          nlinarith
        · -- Show d = (1/2) * a * b
          have h19 : (d : ℚ) = (1 / 2) * (x + z) * (x - z) := by
            nlinarith
          nlinarith
      · -- Assume y < 0
        use x + z, x - z, - (2 * y)
        constructor
        · -- Show a > 0
          nlinarith
        constructor
        · -- Show b > 0
          nlinarith
        constructor
        · -- Show c > 0
          nlinarith
        constructor
        · -- Show a^2 + b^2 = c^2
          nlinarith
        · -- Show d = (1/2) * a * b
          have h19 : (d : ℚ) = (1 / 2) * (x + z) * (x - z) := by
            nlinarith
          nlinarith
    · -- Case where (x + z) < 0 and (x - z) < 0
      have h101 : (x + z) < 0 := h13.1
      have h102 : (x - z) < 0 := h13.2
      have h100 : (y) > 0 ∨ (y) < 0 := by
        by_contra h
        push_neg at h
        have : y = 0 := by linarith
        nlinarith
      rcases h100 with h100 | h100
      · -- Assume y > 0
        use - (x + z), - (x - z), 2 * y
        constructor
        · -- Show a > 0
          nlinarith
        constructor
        · -- Show b > 0
          nlinarith
        constructor
        · -- Show c > 0
          nlinarith
        constructor
        · -- Show a^2 + b^2 = c^2
          nlinarith
        · -- Show d = (1/2) * a * b
          have h19 : (d : ℚ) = (1 / 2) * (x + z) * (x - z) := by
            nlinarith
          nlinarith
      · -- Assume y < 0
        use - (x + z), - (x - z), - (2 * y)
        constructor
        · -- Show a > 0
          nlinarith
        constructor
        · -- Show b > 0
          nlinarith
        constructor
        · -- Show c > 0
          nlinarith
        constructor
        · -- Show a^2 + b^2 = c^2
          nlinarith
        · -- Show d = (1/2) * a * b
          have h19 : (d : ℚ) = (1 / 2) * (x + z) * (x - z) := by
            nlinarith
          nlinarith