import Mathlib

theorem algebra_103895 (a : ℝ) :
    (∃! x : ℝ, x^2 + a^2 * x + 2 * a = 0 ∧ x^2 - 5 * x + 4 ≠ 0) ↔
    a = 0 ∨ a = 2 ∨ a = -1 := by
  constructor
  · -- Assume the existence of a unique x with the property, prove a = 0 ∨ a = 2 ∨ a = -1
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have h1 : x^2 + a^2 * x + 2 * a = 0 := by
      exact hx1.1
    have h2 : x^2 - 5 * x + 4 ≠ 0 := by
      exact hx1.2
    by_cases ha1 : a = 0
    · left
      exact ha1
    by_cases ha2 : a = 2
    · right
      left
      exact ha2
    by_cases ha3 : a = -1
    · right
      right
      exact ha3
    push_neg at ha1 ha2 ha3
    have h_eq5 : ( -a^2 - x )^2 + a^2 * ( -a^2 - x ) + 2 * a = 0 := by
      nlinarith [ h1 ]
    have h_eq7 : ( -a^2 - x )^2 - 5 * ( -a^2 - x ) + 4 = 0 := by
      by_contra hne
      have h_eq7 : ( -a^2 - x ) = x := by
        have h_eq8 : ( -a^2 - x )^2 + a^2 * ( -a^2 - x ) + 2 * a = 0 := h_eq5
        have h_eq9 : ( -a^2 - x )^2 - 5 * ( -a^2 - x ) + 4 ≠ 0 := by
          exact hne
        have h_eq10 : ( -a^2 - x ) = x := by
          apply hx2
          constructor
          · exact h_eq8
          · exact h_eq9
        exact h_eq10
      -- Now from y = x, we derive a contradiction
      -- So from y = x ⇒ -a^2 - x = x ⇒ 2x = -a^2 ⇒ x = -a^2/2
      -- Substituting into x^2 + a^2 x + 2 a = 0 gives a^4 - 8a = 0 ⇒ a = 0 or a = 2
      have h_eq7 : ( -a^2 - x ) = x := h_eq7
      have h_eq8 : x = -a^2 / 2 := by
        nlinarith
      rw [ show x = -a^2 / 2 by linarith [ h_eq8 ] ] at h1
      have h_eq9 : a^4 - 8 * a = 0 := by
        nlinarith
      have h_eq10 : a = 0 ∨ a = 2 := by
        have h_eq11 : a * (a^3 - 8) = 0 := by
          nlinarith
        cases (mul_eq_zero.1 h_eq11) with
        | inl h_eq12 => 
          left; linarith
        | inr h_eq13 => 
          have h_eq14 : a^3 = 8 := by linarith
          have h_eq15 : a = 2 := by
            have h1 : a^3 - 8 = 0 := by linarith
            have h2 : (a - 2) * (a^2 + 2 * a + 4) = 0 := by
              ring_nf at h1 ⊢
              nlinarith
            cases (mul_eq_zero.1 h2) with
            | inl h3 => 
              linarith
            | inr h4 => 
              nlinarith [sq_nonneg (a + 1)]
          right; linarith
      cases h_eq10 with
      | inl ha0 => 
        tauto
      | inr ha2 => 
        tauto
    -- Now we have another root y = -a^2 - x such that y^2 - 5y + 4 = 0
    have h_eq9 : ( -a^2 - x - 1 ) * ( -a^2 - x - 4 ) = 0 := by
      nlinarith [ h_eq7 ]
    cases (mul_eq_zero.1 h_eq9) with
    | inl h_eq10 =>
      have h_eq11 : -a^2 - x = 1 := by linarith
      have h_eq12 : x = -a^2 - 1 := by linarith
      rw [ show x = -a^2 - 1 by linarith [ h_eq12 ] ] at h1
      -- The existence of such a root implies a = -1
      have h_eq13 : (a + 1)^2 = 0 := by
        nlinarith
      have h_eq14 : a + 1 = 0 := by
        apply pow_eq_zero 
        exact h_eq13
      have h_eq15 : a = -1 := by
        linarith
      tauto
    | inr h_eq10 =>
      have h_eq11 : -a^2 - x = 4 := by linarith
      have h_eq12 : x = -a^2 - 4 := by linarith
      rw [ show x = -a^2 - 4 by linarith [ h_eq12  ]  ] at h1
      -- This gives a^4 + 16 = 0
      -- But this has no real roots.
      nlinarith [sq_nonneg (a^2 - 4), sq_nonneg (a^2), sq_nonneg (a^2 - 4*a), sq_nonneg (a - 2), sq_nonneg (a + 2)]
  · -- Assume a = 0 or a = 2 or a = -1, prove the existence of a unique x
    rintro (ha | ha | ha)
    · -- When a = 0
      rw [ha]
      use 0
      constructor
      · -- Show the conditions hold
        constructor
        · norm_num
        · norm_num
      · -- Show x is unique
        intro y hy
        rcases hy with ⟨hy1, hy2⟩
        have hy_eq : y^2 = 0 := by
          nlinarith
        have : y = 0 := by
          nlinarith
        linarith
    · -- When a = 2
      rw [ha]
      use -2
      constructor
      · -- Show the conditions hold
        constructor
        · norm_num
        · norm_num
      · -- Show x is unique
        intro y hy
        rcases hy with ⟨hy1, hy2⟩
        have hy2' : (y + 2)^2 = 0 := by
          nlinarith
        have : y = -2 := by
          nlinarith
        linarith
    · -- When a = -1
      rw [ha]
      use -2
      constructor
      · -- Show the conditions hold
        constructor
        · norm_num
        · norm_num
      · -- Show x is unique
        intro y hy
        rcases hy with ⟨hy1, hy2⟩
        have h_eq5 : (y - 1) * (y + 2) = 0 := by
          nlinarith
        cases (mul_eq_zero.1 h_eq5) with
        | inl h_eq6 =>
          -- y = 1, but 1^2 - 5*1 + 4 = 0
          have h_eq7 : y = 1 := by
            linarith
          rw [h_eq7] at hy2
          norm_num at hy2
        | inr h_eq8 =>
          -- y + 2 = 0 ⇒ y = -2
          have h_eq9 : y = -2 := by
            linarith
          linarith