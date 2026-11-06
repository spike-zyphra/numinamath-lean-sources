import Mathlib

/- 9.103. For what values of $m$ are the roots of the equation $4 x^{2}-(3 m+1) x-m-2=0$ contained in the interval between -1 and 2? -/
theorem algebra_170282 (m : ℝ) (h : ∀ x, 4*x^2 - (3*m+1)*x - m - 2 = 0 → -1 < x ∧ x < 2) :
    m ∈ Set.Ioo (-3/2) (12/7) := by
  -- First we prove the lower bound: m > -3/2
  have h1 : m > -3 / 2 := by
    by_contra h1
    push_neg at h1
    -- If m ≤ -3/2, we'll find a root that's either ≤ -1 or ≥ 2
    have h2 : ∃ x, 4 * x^2 - (3 * m + 1) * x - m - 2 = 0 ∧ (x ≤ -1 ∨ x ≥ 2) := by
      -- We use the smaller root of the quadratic formula
      use (3 * m + 1 - Real.sqrt (9 * m^2 + 22 * m + 33)) / 8
      constructor
      · -- Show that x is a root of the quadratic equation
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        nlinarith [Real.sqrt_nonneg (9 * m^2 + 22 * m + 33)]
      · -- Show that x ≤ -1 or x ≥ 2
        have h3 : (3 * m + 1 - Real.sqrt (9 * m^2 + 22 * m + 33)) / 8 ≤ -1 := by
          -- We prove that sqrt(9m^2 + 22m + 33) ≥ 3m + 9
          have h4 : Real.sqrt (9 * m^2 + 22 * m + 33) ≥ 3 * m + 9 := by
            by_cases h5 : 3 * m + 9 ≤ 0
            · -- Case 1: 3 * m + 9 ≤ 0, then 3 * m + 9 ≤ 0 ≤ sqrt(...)
              nlinarith [Real.sqrt_nonneg (9 * m^2 + 22 * m + 33)]
            · -- Case 2: 3 * m + 9 > 0, then we can square both sides
              have h6 : 0 ≤ Real.sqrt (9 * m^2 + 22 * m + 33) := Real.sqrt_nonneg (9 * m^2 + 22 * m + 33)
              have h7 : Real.sqrt (9 * m^2 + 22 * m + 33) ^ 2 ≥ (3 * m + 9) ^ 2 := by
                nlinarith [Real.sq_sqrt (show 0 ≤ 9 * m^2 + 22 * m + 33 by nlinarith), sq_nonneg (3 * m + 9), h1]
              nlinarith [h6, Real.sqrt_nonneg (9 * m^2 + 22 * m + 33), h7]
          linarith
        left
        linarith
    -- We now have a contradiction with our hypothesis h
    obtain ⟨x, hx1, hx2⟩ := h2
    have hx3 := h x hx1
    cases hx2 with
    | inl h_left =>
      linarith
    | inr h_right =>
      linarith

  -- Next we prove the upper bound: m < 12/7
  have h2 : m < 12 / 7 := by
    by_contra h2
    push_neg at h2
    -- If m ≥ 12/7, we'll find a root that's either ≤ -1 or ≥ 2
    have h3 : ∃ x, 4 * x^2 - (3 * m + 1) * x - m - 2 = 0 ∧ (x ≤ -1 ∨ x ≥ 2) := by
      -- We use the larger root of the quadratic formula
      use (3 * m + 1 + Real.sqrt (9 * m^2 + 22 * m + 33)) / 8
      constructor
      · -- Show that x is a root of the quadratic equation
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        nlinarith [Real.sqrt_nonneg (9 * m^2 + 22 * m + 33)]
      · -- Show that x ≤ -1 or x ≥ 2
        have h4 : (3 * m + 1 + Real.sqrt (9 * m^2 + 22 * m + 33)) / 8 ≥ 2 := by
          -- We prove that sqrt(9m^2 + 22m + 33) ≥ 15 - 3m
          have h5 : Real.sqrt (9 * m^2 + 22 * m + 33) ≥ 15 - 3 * m := by
            by_cases h6 : 15 - 3 * m ≤ 0
            · -- Case 1: 15 - 3m ≤ 0
              nlinarith [Real.sqrt_nonneg (9 * m^2 + 22 * m + 33)]
            · -- Case 2: 15 - 3m > 0
              have h7 : 0 ≤ Real.sqrt (9 * m^2 + 22 * m + 33) := Real.sqrt_nonneg (9 * m^2 + 22 * m + 33)
              have h8 : Real.sqrt (9 * m^2 + 22 * m + 33) ^ 2 ≥ (15 - 3 * m) ^ 2 := by
                nlinarith [Real.sq_sqrt (show 0 ≤ 9 * m^2 + 22 * m + 33 by nlinarith), sq_nonneg (15 - 3 * m), h2]
              nlinarith [h7, Real.sqrt_nonneg (9 * m^2 + 22 * m + 33), h8]
          linarith
        right
        linarith
    -- We now have a contradiction with our hypothesis h
    obtain ⟨x, hx1, hx2⟩ := h3
    have hx3 := h x hx1
    cases hx2 with
    | inl h_left =>
      linarith
    | inr h_right =>
      linarith

  -- Combine both bounds to get the final result
  exact ⟨h1, h2⟩
