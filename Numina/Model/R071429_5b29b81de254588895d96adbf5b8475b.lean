import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_302246 (x : ℝ) (hx : x ≠ 2) :
    (x^2 - 2 * x - 15) / (x - 2) < 0 ↔ x ∈ Ioo 2 5 ∪ Iio (-3) := by
  have h1 : x^2 - 2*x - 15 = (x - 5) * (x + 3) := by
    ring
  have h1' : (x^2 - 2*x - 15) / (x - 2) = (x - 5) * (x + 3) / (x - 2) := by
    rw [h1]
  rw [h1']
  constructor
  · -- Forward direction: if (x - 5) * (x + 3) / (x - 2) < 0 then x ∈ (2, 5) ∪ (-∞, -3)
    intro h
    have h2 : (x - 5) * (x + 3) / (x - 2) < 0 := by linarith
    have h3 : x - 2 ≠ 0 := by
      intro h4
      apply hx
      linarith
    apply div_neg_iff.mp at h2
    cases h2 with
    | inl h4 =>
      -- Case where (x - 5) * (x + 3) > 0 and x - 2 < 0, so x < 2 and (x > 5 or x < -3), which gives x < -3
      have h5 : (x - 5) * (x + 3) > 0 := by linarith
      have h6 : x - 2 < 0 := by linarith
      have h7 : x < 2 := by linarith
      have h8 : x < -3 := by nlinarith
      -- Therefore x ∈ (-∞, -3)
      right
      exact h8
    | inr h4 =>
      -- Case where (x - 5) * (x + 3) < 0 and x - 2 > 0, so x > 2 and (-3 < x < 5), which gives 2 < x < 5
      have h5 : (x - 5) * (x + 3) < 0 := by linarith
      have h6 : x - 2 > 0 := by linarith
      have h7 : x > 2 := by linarith
      have h8 : -3 < x ∧ x < 5 := by
        constructor
        · nlinarith
        · nlinarith
      -- Therefore x ∈ (2, 5)
      left
      constructor
      · linarith
      · linarith
  · -- Backward direction: if x ∈ (2, 5) ∪ (-∞, -3) then (x - 5) * (x + 3) / (x - 2) < 0
    rintro (h | h)
    · -- Case where x ∈ (2, 5)
      have h1 : 2 < x := h.1
      have h2 : x < 5 := h.2
      have h3 : x - 2 > 0 := by linarith
      have h4 : x + 3 > 0 := by nlinarith
      have h5 : x - 5 < 0 := by linarith
      have h6 : (x - 5) * (x + 3) < 0 := by nlinarith
      apply div_neg_of_neg_of_pos
      · linarith
      · linarith
    · -- Case where x ∈ (-∞, -3)
      have h1 : x < -3 := h
      have h3 : x - 2 < 0 := by linarith
      have h4 : x + 3 < 0 := by linarith
      have h5 : x - 5 < 0 := by linarith
      have h6 : (x - 5) * (x + 3) > 0 := by nlinarith
      apply div_neg_of_pos_of_neg
      · linarith
      · linarith