import Mathlib

theorem algebra_13680 (A B : ℝ) (hA : A ≠ B) (h : ∀ x, x ≠ A ∧ x ≠ B → 2*x^2-6*x+4 ≠ 0) :
    A + B = 3 := by
  -- Show that 1 is a root of the quadratic.
  have h1 : (2 * (1 : ℝ) ^ 2 - 6 * (1 : ℝ) + 4) = 0 := by norm_num
  -- Show that 2 is a root of the quadratic.
  have h2 : (2 * (2 : ℝ) ^ 2 - 6 * (2 : ℝ) + 4) = 0 := by norm_num
  have h1' : A = 1 ∨ B = 1 := by
    by_contra h12
    push_neg at h12
    have h3 := h 1 ⟨by
      intro h4
      apply h12.1
      all_goals
        linarith
    , by
      intro h4
      apply h12.2
      all_goals
        linarith
    ⟩
    norm_num at h3
  have h2' : A = 2 ∨ B = 2 := by
    by_contra h12
    push_neg at h12
    have h3 := h 2 ⟨by
      intro h4
      apply h12.1
      all_goals
        linarith
    , by
      intro h4
      apply h12.2
      all_goals
        linarith
    ⟩
    norm_num at h3
  cases h1' with
  | inl h1l =>
    cases h2' with
    | inl h2l =>
      -- $A = 1, A = 2$: contradiction
      linarith
    | inr h2r =>
      -- $A = 1, B = 2$
      linarith
  | inr h1r =>
    cases h2' with
    | inl h2l =>
      -- $A = 2, b = 1$
      linarith
    | inr h2r =>
      -- $b = 1, b = 2$: contradiction
      linarith