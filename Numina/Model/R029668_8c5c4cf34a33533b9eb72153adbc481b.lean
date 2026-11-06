import Mathlib

open Real Set
open scoped BigOperators

/- The domain of the function $y=\frac{1}{\sqrt{{{x}^{2}}-6x+8}}+{{\log }_{2}}\left( \frac{x+3}{x-1}-2 \right)$ is ___        ___. -/
theorem algebra_12589 (x : ℝ) :
  x ∈ (Set.Ioo 1 2) ∪ (Set.Ioo 4 5) ↔
  0 < (x^2 - 6 * x + 8) ∧ (x + 3) / (x - 1) - 2 > 0 := by
  constructor
  · -- Forward: if x ∈ (1, 2) ∪ (4, 5) then 0 < (x^2 - 6 * x + 8) ∧ (x + 3) / (x - 1) - 2 > 0
    rintro (h | h)
    · -- Case where x ∈ (1, 2)
      rcases h with ⟨hx1, hx2⟩
      constructor
      · -- Show 0 < (x^2 - 6 * x + 8)
        nlinarith
      · -- Show (x + 3) / (x - 1) - 2 > 0
        have h1 : x - 1 > 0 := by linarith
        have h2 : (x + 3) / (x - 1) - 2 > 0 := by
          have h3 : (x + 3) / (x - 1) - 2 = (-x + 5) / (x - 1) := by
            field_simp [(show x - 1 ≠ 0 by linarith)]
            <;> ring
          rw [h3]
          apply div_pos
          · -- Show -x + 5 > 0
            linarith
          · -- Show x - 1 > 0
            linarith
        linarith
    · -- Case where x ∈ (4, 5)
      rcases h with ⟨hx1, hx2⟩
      constructor
      · -- Show 0 < (x^2 - 6 * x + 8)
        nlinarith
      · -- Show (x + 3) / (x - 1) - 2 > 0
        have h1 : x - 1 > 0 := by linarith
        have h2 : (x + 3) / (x - 1) - 2 > 0 := by
          have h3 : (x + 3) / (x - 1) - 2 = (-x + 5) / (x - 1) := by
            field_simp [(show x - 1 ≠ 0 by linarith)]
            <;> ring
          rw [h3]
          apply div_pos
          · -- Show -x + 5 > 0
            linarith
          · -- Show x - 1 > 0
            linarith
        linarith
  · -- Backward: if 0 < (x^2 - 6 * x + 8) ∧ (x + 3) / (x - 1) - 2 > 0 then x ∈ (1, 2) ∪ (4, 5)
    rintro ⟨h1, h2⟩
    have h3 : (x - 1) > 0 := by
      by_contra h
      push_neg at h
      have h4 : (x + 3) / (x - 1) - 2 ≤ 0 := by
        have h5 : (x - 1) ≤ 0 := by nlinarith
        have h6 : (x + 3) / (x - 1) - 2 ≤ 0 := by
          have h7 : (x + 3) / (x - 1) - 2 = (-x + 5) / (x - 1) := by
            field_simp [(show x - 1 ≠ 0 from by
              by_contra h8
              have : x = 1 := by linarith
              rw [this] at h2
              norm_num at h2
            )]
            <;> ring
          rw [h7]
          apply div_nonpos_of_nonneg_of_nonpos
          · -- Show -x + 5 ≥ 0
            nlinarith
          · -- Show x - 1 ≤ 0
            nlinarith
        linarith
      linarith
    have h4 : (x + 3) / (x - 1) - 2 > 0 := h2
    have h5 : x > 1 := by
      have h6 : (x - 1) > 0 := h3
      nlinarith
    have h6 : x < 5 := by
      have h7 : (x + 3) / (x - 1) - 2 > 0 := h2
      have h8 : (x + 3) / (x - 1) - 2 = (-x + 5) / (x - 1) := by
        field_simp [(show x - 1 ≠ 0 by linarith)]
        <;> ring
      rw [h8] at h7
      apply div_pos_iff.mp at h7
      cases h7 with
      | inl h =>
        nlinarith
      | inr h =>
        nlinarith
    have h2 : x^2 - 6 * x + 8 > 0 := h1
    have h3 : x < 2 ∨ x > 4 := by
      by_contra h
      push_neg at h
      nlinarith
    cases h3 with
    | inl h7 =>
      left
      constructor <;> linarith
    | inr h7 =>
      right
      constructor <;> linarith