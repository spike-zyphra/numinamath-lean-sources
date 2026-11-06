import Mathlib

theorem algebra_20317 (x : ℝ) (hx : x ≠ 1) : (x + 7) * (x - 2) / (x - 1) < 0 ↔
    x < -7 ∨ x ∈ Set.Ioo 1 2 := by 
  constructor
  · -- Forward direction: if (x + 7) * (x - 2) / (x - 1) < 0, then x < -7 ∨ x ∈ Set.Ioo 1 2
    intro h
    have h1 : (x - 1) ≠ 0 := by
      intro h2
      apply hx
      linarith
    apply div_neg_iff.mp at h
    cases h with
    | inl h2 =>
      have h3 : (x + 7) * (x - 2) > 0 := by linarith
      have h4 : x - 1 < 0 := by linarith
      cases mul_pos_iff.mp h3 with
      | inl h5 =>
        exfalso
        linarith
      | inr h6 =>
        left
        linarith
    | inr h2 =>
      have h3 : (x + 7) * (x - 2) < 0 := by linarith
      have h4 : x - 1 > 0 := by linarith
      cases mul_neg_iff.mp h3 with
      | inl h5 =>
        right
        have h6 : 1 < x := by linarith
        have h7 : x < 2 := by linarith
        exact ⟨h6, h7⟩
      | inr h6 =>
        exfalso
        linarith
  · -- Backward direction: if x < -7 ∨ x ∈ Set.Ioo 1 2, then (x + 7) * (x - 2) / (x - 1) < 0
    intro h
    cases h with
    | inl h1 =>
      have h2 : (x + 7) * (x - 2) > 0 := by
        have h3 : (x + 7) < 0 := by linarith
        have h4 : (x - 2) < 0 := by linarith
        have h5 : (x + 7) * (x - 2) > 0 := mul_pos_of_neg_of_neg h3 h4
        exact h5
      have h3 : (x - 1) < 0 := by linarith
      apply div_neg_of_pos_of_neg
      linarith
      linarith
    | inr h2 =>
      have h3 : x - 1 > 0 := by
        have h4 : 1 < x := h2.1
        linarith
      have h4 : (x + 7) > 0 := by 
        linarith 
      have h5 : x - 2 < 0 := by 
        have h6 : x < 2 := h2.2
        linarith
      have h6 : (x + 7) * (x - 2) < 0 := mul_neg_of_pos_of_neg h4 (show x - 2 < 0 by linarith)
      apply div_neg_of_neg_of_pos
      linarith
      linarith