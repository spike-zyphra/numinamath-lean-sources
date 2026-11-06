import Mathlib

theorem algebra_14010 : {x : ℝ | x ≠ -3 ∧ x / (x + 3) ≥ 0} = Set.Iio (-3) ∪ Set.Ici 0 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ici]
  constructor
  · -- Assume x in the left side, prove it's in the right side
    rintro ⟨hx1, hx2⟩
    by_cases h3 : x + 3 > 0
    · -- x + 3 > 0, so x > -3
      have h4 : x ≥ 0 := by
        apply (div_nonneg_iff).mp at hx2
        cases hx2 with
        | inl h1l =>
          linarith
        | inr h1r =>
          nlinarith
      right
      linarith
    by_cases h4 : x + 3 < 0
    · -- x + 3 < 0, so x < -3
      have h5 : x < -3 := by linarith
      left
      linarith
    · -- x + 3 = 0, so x = -3
      have h5 : x + 3 = 0 := by
        linarith
      have h6 : x = -3 := by linarith
      contradiction
  · -- Now the reverse direction
    rintro (h | h)
    · -- x < -3
      have hx1 : x < -3 := h
      constructor
      · -- Show x ≠ -3
        by_contra h2
        linarith
      · -- Show x / (x + 3) ≥ 0
        have hx1 : x < -3 := h
        have hx3 : x + 3 < 0 := by linarith
        have hx4 : x < 0 := by linarith
        apply div_nonneg_of_nonpos
        · -- Show x ≤ 0
          linarith
        · -- Show x + 3 ≤ 0
          linarith
    · -- x ≥ 0
      have hx2 : x ≥ 0 := h
      constructor
      · -- Show x ≠ -3
        by_contra h2
        have hx3 : x = -3 := by linarith
        linarith -- contradiction with x ≥ 0
      · -- Show x / (x + 3) ≥ 0
        have hx2 : x ≥ 0 := h
        have hx3 : x + 3 > 0 := by linarith
        apply div_nonneg
        · -- Show x ≥ 0
          linarith
        · -- Show x + 3 ≥ 0
          linarith