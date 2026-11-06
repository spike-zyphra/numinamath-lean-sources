import Mathlib

theorem inequalities_189998 (x : ℝ) (hx : x^2 - 4 * x - 5 ≠ 0) :
    (x^4 + x^2 + 1) / (x^2 - 4 * x - 5) < 0 ↔ x ∈ Set.Ioo (-1) 5 := by
  have h1 : x^4 + x^2 + 1 > 0 := by
    nlinarith [sq_nonneg (x^2), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1)]
  have h2 : (x^4 + x^2 + 1) / (x^2 - 4 * x - 5) < 0 ↔ (x^4 + x^2 + 1) > 0 ∧ (x^2 - 4 * x - 5) < 0 := by
    apply Iff.intro
    · -- Assume the fraction is negative, prove the conjunction
      intro h
      apply div_neg_iff.mp at h
      cases h with
      | inl h1 =>
        constructor
        · linarith
        · linarith
      | inr h2 =>
        nlinarith
    · -- Assume the conjunction, prove the fraction is negative
      rintro ⟨h1, h2⟩
      apply div_neg_iff.mpr
      left
      constructor
      · linarith
      · linarith
  rw [h2]
  constructor
  · -- Assume the conjunction, prove x ∈ (-1,5)
    intro h
    rcases h with ⟨h_num, h_den⟩
    constructor
    · -- Show that -1 < x
      nlinarith
    · -- Show that x < 5
      nlinarith
  · -- Assume x ∈ (-1,5), prove the conjunction
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that x^4 + x^2 +1 >0
      nlinarith [sq_nonneg (x^2), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    · -- Show that x^2 -4x -5 <0
      nlinarith