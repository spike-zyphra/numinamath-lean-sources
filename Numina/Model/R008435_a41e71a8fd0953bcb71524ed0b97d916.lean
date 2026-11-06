import Mathlib

theorem inequalities_575707 : {x : ℝ | abs (x^2 - 2) < 2} = Set.Ioo (-2) 0 ∪ Set.Ioo 0 2 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo]
  constructor
  · -- Assume h: abs (x^2 - 2) < 2, prove ⊢ Set.Ioo (-2) 0 ∪ Set.Ioo 0 2
    intro h
    have h1 : -2 < x^2 - 2 := by linarith [abs_lt.mp h]
    have h2 : x^2 - 2 < 2 := by linarith [abs_lt.mp h]
    have h3 : 0 < x^2 := by linarith
    have h4 : x^2 < 4 := by linarith
    have h5 : -2 < x := by nlinarith
    have h6 : x < 2 := by nlinarith
    have h7 : x ≠ 0 := by
      by_contra h0
      rw [show x = (0 : ℝ) by linarith] at h3
      linarith
    have h8 : x < 0 ∨ 0 < x := by
      by_contra h9
      push_neg at h9
      have h9' : x = 0 := by
        linarith
      contradiction
    cases h8 with
    | inl h8 =>
      -- Case x < 0
      left
      constructor
      · linarith
      · linarith
    | inr h8 =>
      -- Case 0 < x
      right
      constructor
      · linarith
      · linarith
  · -- Assume x ∈ Set.Ioo (-2) 0 ∪ Set.Ioo 0 2, prove abs (x^2 - 2) < 2
    rintro (h | h)
    · -- Case x ∈ (-2, 0)
      have h1 : -2 < x := h.1
      have h2 : x < 0 := h.2
      have h3 : 0 < x ^ 2 := by nlinarith
      have h4 : x^2 < 4 := by nlinarith
      have h1' : -2 < x^2 - 2 := by linarith
      have h2' : x^2 - 2 < 2 := by linarith
      apply abs_lt.mpr
      constructor
      · linarith
      · linarith
    · -- Case x ∈ (0, 2)
      have h1 : 0 < x := h.1
      have h2 : x < 2 := h.2
      have h3 : 0 < x ^ 2 := by nlinarith
      have h4 : x^2 < 4 := by nlinarith
      have h1' : -2 < x^2 - 2 := by linarith
      have h2' : x^2 - 2 < 2 := by linarith
      apply abs_lt.mpr
      constructor
      · linarith
      · linarith