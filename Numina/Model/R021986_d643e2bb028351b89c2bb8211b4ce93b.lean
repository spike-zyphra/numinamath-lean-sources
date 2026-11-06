import Mathlib

theorem algebra_200577 (x y : ℤ) :
    x ≥ 0 ∧ y ≥ 0 ∧ x^3 + 8 * x^2 - 6 * x + 8 = y^3 ↔ (x, y) = (0, 2) ∨ (x, y) = (9, 11) := by 
  constructor
  · -- Assume the left side: x ≥ 0 ∧ y ≥ 0 ∧ x^3 + 8 * x^2 - 6 * x + 8 = y^3, prove (x, y) = (0, 2) ∨ (x, y) = (9, 11)
    rintro ⟨hx, hy, h⟩
    have h1 : y ≤ x + 3 := by
      nlinarith [sq_nonneg ((x + 3) ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg ((x + 3) - y), sq_nonneg (y - (x + 3))]
    by_cases h3 : x ≤ 8
    · -- Case where x ≤ 8
      interval_cases x <;> 
        try { 
          have : y ≤ 12 := by
            nlinarith [sq_nonneg (y - 12), sq_nonneg (y + 12)]
          interval_cases y <;> norm_num at h <;> tauto 
        }
    · -- Case where x ≥ 9
      have h4 : x ≥ 9 := by
        omega 
      have h2 : y ≥ x + 2 := by
        nlinarith [sq_nonneg ((x + 2) ^ 2 - y ^ 2), sq_nonneg (x + 2 - y), sq_nonneg (x + 2 + y), sq_nonneg (x - y), sq_nonneg (y - (x + 2)), sq_nonneg (y ^ 2 - (x + 2) ^ 2)]
      have h3 : y = x + 2 ∨ y = x + 3 := by 
        omega 
      cases h3 with
      | inl h4 =>
        rw [show y = x + 2 by linarith [h4]] at h
        have h2 : x = 0 ∨ x = 9 := by 
          have h3 : 2 * x^2 - 18 * x = 0 := by 
            nlinarith 
          have h4 : x * (x - 9) = 0 := by 
            nlinarith 
          cases (mul_eq_zero.mp h4) with
          | inl h5 => 
            left 
            linarith 
          | inr h6 => 
            right 
            linarith 
        cases h2 with
        | inl h0 => 
          have h00 : x = 0 := h0 
          have h01 : y = 2 := by 
            linarith [h4, h00] 
          simp [Prod.ext_iff, h00, h01]
        | inr h9 => 
          have h99 : x = 9 := h9 
          have h911 : y = 11 := by 
            linarith [h4, h99] 
          simp [Prod.ext_iff, h99, h911]
      | inr h5 => 
        rw [show y = x + 3 by linarith [h5]] at h 
        have h2 : x ^ 2 + 33 * x + 19 = 0 := by 
          nlinarith 
        nlinarith [sq_nonneg (x + 16)]
  · -- Backward direction: (x, y) = (0, 2) ∨ (x, y) = (9, 11) prove x ≥ 0 ∧ y ≥ 0 ∧ x^3 + 8 * x^2 - 6 * x + 8 = y^3
    rintro (h | h)
    · -- Case (0, 2)
      simp [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Case (9, 11)
      simp [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num