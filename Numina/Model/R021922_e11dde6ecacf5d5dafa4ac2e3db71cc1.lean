import Mathlib

theorem algebra_15097 (x : ℝ) (hx : x ≠ 3) : (x - 1) / (x - 3) ≥ 2 ↔ 3 < x ∧ x ≤ 5 := by
  constructor
  · -- Forward direction: if (x - 1) / (x - 3) ≥ 2, then 3 < x ∧ x ≤ 5
    intro h
    have h1 : x - 3 ≠ 0 := by
      intro h2
      apply hx
      linarith

    by_cases h2 : x - 3 > 0
    · -- Case where x - 3 > 0, so x > 3
      have h3 : x > 3 := by linarith
      have h4 : x - 1 ≥ 2 * (x - 3) := by
        have h5 : (x - 1) / (x - 3) ≥ 2 := h
        have h8 : x - 3 > 0 := h2
        apply (le_div_iff₀ h8).mp at h
        linarith
      have h5 : x ≤ 5 := by linarith
      constructor
      · -- Show that 3 < x
        linarith
      · -- Show that x ≤ 5
        linarith

    by_cases h2 : x - 3 < 0
    · -- Case where x - 3 < 0, so x < 3
      have h3 : x < 3 := by linarith
      -- Multiply both sides by x - 3 which is negative, so the inequality reverses
      have h4 : x - 1 ≤ 2 * (x - 3) := by
        have h5 : (x - 1) / (x - 3) ≥ 2 := h
        have h6 : (x - 3) < 0 := h2
        apply (le_div_iff_of_neg' h6).mp at h
        linarith
      -- From h4 we know x >= 5
      have h5 : x ≥ 5 := by linarith
      -- This is a contradiction as x < 3 and x >= 5
      linarith

    -- x - 3 is neither positive nor negative, so it must be 0, which is excluded by hypothesis
    have h6 : x - 3 = 0 := by linarith
    contradiction

  · -- Backward direction: if 3 < x ∧ x ≤ 5, then (x - 1) / (x - 3) ≥ 2
    rintro ⟨h1, h2⟩
    -- First establish that x - 3 > 0
    have h3 : x - 3 > 0 := by linarith
    -- We need to show (x - 1) / (x - 3) >= 2
    -- Multiply both sides by x - 3 which is positive, so inequality remains
    have h4 : x - 1 ≥ 2 * (x - 3) := by
      linarith
    have h5 : (x - 1) / (x - 3) ≥ 2 := by
      have h6 : x - 3 > 0 := h3
      apply (le_div_iff₀ h6).mpr
      linarith
    linarith