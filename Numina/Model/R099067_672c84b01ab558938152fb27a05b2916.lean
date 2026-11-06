import Mathlib

theorem inequalities_6259 (x : ℝ) (hx : x ≠ 1) :
    x / (x - 1) > 4 ↔ 1 < x ∧ x < 4 / 3 := by
  constructor
  · -- Forward direction: If $\frac{x}{x-1} > 4$, prove $1 < x ∧ x < 4 / 3$
    intro h
    have h1 : x - 1 ≠ 0 := by
      intro h'
      apply hx
      linarith
    have h2 : x / (x - 1) - 4 > 0 := by linarith
    have h3 : (x - 4 * (x - 1)) / (x - 1) > 0 := by
      have h11 : x / (x - 1) - 4 = (x - 4 * (x - 1)) / (x - 1) := by
        field_simp [(show x - 1 ≠ 0 by assumption)]
        <;> ring
      linarith [h11, h2]
    have h4 : (x - 4 * (x - 1)) / (x - 1) = (4 - 3 * x) / (x - 1) := by
      field_simp [(show x - 1 ≠ 0 by assumption)]
      <;> ring
    have h5 : (4 - 3 * x) / (x - 1) > 0 := by linarith [h3, h4]
    have h6 : ((4 - 3 * x) / (x - 1) > 0) ↔ ((4 - 3 * x) > 0 ∧ (x - 1) > 0) ∨ ((4 - 3 * x) < 0 ∧ (x - 1) < 0) := by
      apply Iff.intro
      · -- Forward implication: if $\frac{N}{D} > 0$, then either $N > 0 \land D > 0$ or $N < 0 \land D < 0$
        intro h
        apply div_pos_iff.mp at h
        exact h
      · -- Backward implication: if either $N > 0 \land D > 0$ or $N < 0 \land D < 0$, then $\frac{N}{D} > 0$
        rintro (h | h)
        · -- Case $N > 0 \land D > 0$
          apply div_pos_iff.mpr
          exact Or.inl h
        · -- Case $N < 0 \land D < 0$
          apply div_pos_iff.mpr
          exact Or.inr h
    cases (h6.mp h5) with
    | inl h_pos =>
      constructor
      · -- Proving x > 1 from x - 1 > 0
        linarith [h_pos.right]
      · -- Proving x < 4/3 from 4 - 3x > 0
        linarith [h_pos.left]
    | inr h_neg =>
      linarith [h_neg.left, h_neg.right]
  · -- Backward direction: If $1 < x ∧ x < 4 / 3$, prove $\frac{x}{x - 1} > 4$
    rintro ⟨h1, h2⟩
    have h3 : x - 1 > 0 := by linarith
    have h4 : x / (x - 1) - 4 > 0 := by
      have h5 : (x / (x - 1) - 4) = (x - 4 * (x - 1)) / (x - 1) := by
        field_simp [(show x - 1 ≠ 0 by linarith)]
        <;> ring
      rw [h5]
      have h6 : x - 4 * (x - 1) > 0 := by linarith
      have h7 : (x - 1) > 0 := by linarith
      apply div_pos
      linarith
      linarith
    linarith [h4]