import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_189877 (x : ℝ) :
  (1 / (x + 2) < 3 / (x - 3)) ↔
  (x ∈ Ioo (-9 / 2) (-2) ∪ Ioi 3) := by
  constructor
  · -- Assume $\frac{1}{x+2} < \frac{3}{x - 3}$, prove $x \in (-\frac{9}{2}, -2) \cup (3, \infty)$
    intro h
    have h1 : x - 3 ≠ 0 := by
      by_contra h2
      have h3 : x = 3 := by linarith
      rw [h3] at h
      norm_num at h
    have h2 : x + 2 ≠ 0 := by
      by_contra h3
      have h4 : x = -2 := by linarith
      rw [h4] at h
      norm_num at h
    have h3 : (1 / (x + 2) - 3 / (x - 3)) < 0 := by linarith
    have h4 : (1 / (x + 2) - 3 / (x - 3)) = (-2 * x - 9) / ((x + 2) * (x - 3)) := by
      field_simp [(show x + 2 ≠ 0 by assumption), (show x - 3 ≠ 0 by assumption)]
      <;> ring
    rw [h4] at h3
    have h5 : (x + 2) * (x - 3) ≠ 0 := by
      apply mul_ne_zero
      · exact h2
      · exact h1
    apply div_neg_iff.mp at h3
    cases h3 with
    | inl h1 =>
      exfalso
      nlinarith
    | inr h2 =>
      have h5 : x > -9 / 2 := by linarith
      have h6 : (x + 2) * (x - 3) > 0 := by nlinarith
      have h7 : x < -2 ∨ x > 3 := by
        by_contra h
        push_neg at h
        nlinarith [h6]
      cases h7 with
      | inl h8 =>
        left
        constructor <;> linarith
      | inr h9 =>
        right
        exact h9
  · -- Assume $x \in (-\frac{9}{2}, -2) \cup (3, \infty)$, prove $\frac{1}{x+2} < \frac{3}{x - 3}$
    intro h
    rcases h with (h | h)
    · -- Case where x ∈ (-9/2, -2)
      rcases h with ⟨h1, h2⟩
      have h3 : x + 2 < 0 := by nlinarith
      have h4 : x - 3 < 0 := by nlinarith
      have h5 : (1 / (x + 2) - 3 / (x - 3)) < 0 := by
        have h4' : (1 / (x + 2) - 3 / (x - 3)) = (-2 * x - 9) / ((x + 2) * (x - 3)) := by
          field_simp [(show x + 2 ≠ 0 by nlinarith), (show x - 3 ≠ 0 by nlinarith)]
          <;> ring
        rw [h4'] at *
        apply div_neg_of_neg_of_pos
        · -- Show -2 * x - 9 < 0
          nlinarith
        · -- Show (x + 2) * (x - 3) > 0
          nlinarith
      linarith
    · -- Case where x ∈ (3, ∞)
      rcases h with h
      have h4 : x > 3 := by
        have h5 : x ∈ Ioi (3 : ℝ) := h
        simpa using h5
      have h3 : x - 3 > 0 := by
        nlinarith
      have h5 : x + 2 > 0 := by
        nlinarith
      have h6 : (1 / (x + 2) - 3 / (x - 3)) < 0 := by
        have h4' : (1 / (x + 2) - 3 / (x - 3)) = (-2 * x - 9) / ((x + 2) * (x - 3)) := by
          field_simp [(show x + 2 ≠ 0 by nlinarith), (show x - 3 ≠ 0 by nlinarith)]
          <;> ring
        rw [h4'] at *
        apply div_neg_of_neg_of_pos
        · -- Show -2 * x - 9 < 0
          nlinarith
        · -- Show (x + 2) * (x - 3) > 0
          nlinarith
      linarith