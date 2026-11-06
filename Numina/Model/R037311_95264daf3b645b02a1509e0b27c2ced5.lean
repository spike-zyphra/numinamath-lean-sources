import Mathlib

theorem algebra_12931 : {x : ℝ | (x^2 - 2 * x + 3 ≠ 0) ∧ (-1 < (x^2 - 14 * x + 11) / (x^2 - 2 * x + 3)) ∧ ((x^2 - 14 * x + 11) / (x^2 - 2 * x + 3) < 1)} = Set.Ioo (2/3) 1 ∪ Set.Ioi 7 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · -- Assume x in the left side; prove it's in the right side
    rintro ⟨hx1, h1, h2⟩
    have h_pos : x^2 - 2 * x + 3 > 0 := by
      nlinarith [sq_nonneg (x - 1)]
    have h3 : -1 < (x^2 - 14 * x + 11) / (x^2 - 2 * x + 3) := h1
    have h1' : -(x^2 - 2 * x + 3) < x^2 - 14 * x + 11 := by
      have h2' : (x^2 - 2 * x + 3) > 0 := h_pos
      apply (lt_div_iff₀ h2').mp at h3
      linarith
    have h5 : 0 < x^2 - 8 * x + 7 := by
      nlinarith
    have h5' : (x < 1) ∨ (x > 7) := by
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 7)]
    have h4 : (x^2 - 14 * x + 11) / (x^2 - 2 * x + 3) < 1 := h2
    have h4' : (x^2 - 14 * x + 11) < (x^2 - 2 * x + 3) := by
      have h2' : (x^2 - 2 * x + 3) > 0 := h_pos
      apply (div_lt_iff₀ h2').mp at h4
      linarith
    have h6 : x > (2 / 3) := by
      nlinarith
    cases h5' with
    | inl h9 =>
      left
      have h7 : x < 1 := h9
      have h8 : x > (2 / 3) := h6
      exact ⟨h8, h7⟩
    | inr h6 =>
      right
      have h5 : x > (7) := h6
      exact h5
  · -- Assume x in the right side; prove it's in the left side
    rintro (h | h)
    · -- Case $\frac{2}{3} < x < 1$
      rcases h with ⟨h1, h2⟩
      have h_pos : x^2 - 2 * x + 3 > 0 := by
        nlinarith [sq_nonneg (x - 1)]
      have hx1 : x^2 - 2 * x + 3 ≠ 0 := by
        linarith
      have h3 : -1 < (x^2 - 14 * x + 11) / (x^2 - 2 * x + 3) := by
        have h4 : (x^2 - 2 * x + 3) > 0 := h_pos
        apply (lt_div_iff₀ h4).mpr
        nlinarith
      have h4 : (x^2 - 14 * x + 11) / (x^2 - 2 * x + 3) < 1 := by
        have h4 : (x^2 - 2 * x + 3) > 0 := h_pos
        apply (div_lt_iff₀ h4).mpr
        nlinarith
      exact ⟨hx1, h3, h4⟩
    · -- Case $x > 7$
      have hx1 : x > 7 := h
      have h_pos : x^2 - 2 * x + 3 > 0 := by
        nlinarith [sq_nonneg (x - 1)]
      have hx1' : x^2 - 2 * x + 3 ≠ 0 := by
        linarith
      have h3 : -1 < (x^2 - 14 * x + 11) / (x^2 - 2 * x + 3) := by
        have h4 : (x^2 - 2 * x + 3) > 0 := h_pos
        apply (lt_div_iff₀ h4).mpr
        nlinarith
      have h4 : (x^2 - 14 * x + 11) / (x^2 - 2 * x + 3) < 1 := by
        have h4 : (x^2 - 2 * x + 3) > 0 := h_pos
        apply (div_lt_iff₀ h4).mpr
        nlinarith
      exact ⟨hx1', h3, h4⟩