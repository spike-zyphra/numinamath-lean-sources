import Mathlib

theorem algebra_147601 (a : ℝ) :
    ∃ x, Real.cos (2 * x) ^ 4 - 2 * (a + 2) * Real.cos (2 * x) ^ 2 - (2 * a + 5) = 0 ↔
    a ∈ Set.Icc (-2.5) (-2) := by

  -- Consider two cases based on the bounds of a
  by_cases h : a ≤ -2

  · -- If a ≤ -2, we can find a solution using arccos
    use Real.arccos (Real.sqrt (2 * a + 5)) / 2
    constructor
    · -- Forward direction: equation implies a ∈ interval
      intro h_eq
      -- Show that a ≤ -2 from h
      constructor
      · -- Show that -2.5 ≤ a
        nlinarith [Real.sqrt_nonneg (2 * a + 5), Real.sq_sqrt (show (2 * a + 5) ≥ 0 by nlinarith), h_eq]
      · -- Show that a ≤ -2
        exact h
    · -- Backward direction: a ∈ interval implies equation
      rintro ⟨h1, h2⟩
      -- Verify squaring and taking square roots
      have hcos : Real.cos (2 * (Real.arccos (Real.sqrt (2 * a + 5)) / 2)) = Real.sqrt (2 * a + 5) := by
        have h1 : Real.cos ( Real.arccos (Real.sqrt (2 * a + 5)) ) = Real.sqrt (2 * a + 5) := by
          apply Real.cos_arccos
          all_goals
            nlinarith [Real.sqrt_nonneg (2 * a + 5), Real.sq_sqrt (show (2 * a + 5) ≥ 0 by nlinarith)]
        have h2 : 2 * (Real.arccos (Real.sqrt (2 * a + 5)) / 2) = Real.arccos (Real.sqrt (2 * a + 5)) := by
          ring_nf
        rw [h2]
        linarith [h1]
      simp [hcos]
      <;> nlinarith [Real.sqrt_nonneg (2 * a + 5), Real.sq_sqrt (show (2 * a + 5) ≥ 0 by nlinarith), sq_nonneg (Real.sqrt (2 * a + 5)), h]

  · -- If a > -2, use a contradiction
    use 0  -- Use a trivial witness for the contradiction
    constructor
    · -- Forward direction: equation implies a ∈ interval
      intro h_eq
      -- Show a contradiction
      have h1 : -2 < a := by
        linarith
      exfalso
      nlinarith [Real.cos_sq_add_sin_sq (2 * (0 : ℝ)), h_eq, h1]
    · -- Backward direction: a ∈ interval implies equation
      intro h
      -- Show a contradiction
      exfalso
      have h1 : a ≤ -2 := by
        have h2 : a ≤ -2 := by
          have h3 : a ∈ Set.Icc (-2.5) (-2) := h
          simp at h3 ⊢
          all_goals linarith
        linarith
      -- Compare with assumption 'a > -2' and 'a ≤ -2'
      linarith