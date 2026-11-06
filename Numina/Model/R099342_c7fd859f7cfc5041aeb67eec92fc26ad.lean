import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_284652 (m : ℝ) :
  {x | (x^2 - 8 * x + 20) / (m * x^2 + 2 * (m + 1) * x + 9 * m + 4) < 0} = ⊤ ↔
  m < -1 / 2 := by
  constructor
  · -- First direction: if the set is equal to ⊤, then m < -1/2
    intro h
    have h1 : ∀ x : ℝ, (x ^ 2 - 8 * x + 20) / (m * x ^ 2 + 2 * (m + 1) * x + 9 * m + 4) < 0 := by
      simp [Set.ext_iff] at h ⊢
      simpa using h
    have h2 : ∀ x : ℝ, x ^ 2 - 8 * x + 20 > 0 := by
      intro x
      nlinarith [sq_nonneg (x - 4)]
    have h3 : ∀ x : ℝ, m * x ^ 2 + 2 * (m + 1) * x + 9 * m + 4 < 0 := by
      intro x
      have h4 : (x ^ 2 - 8 * x + 20) / (m * x ^ 2 + 2 * (m + 1) * x + 9 * m + 4) < 0 := h1 x
      have h5 : (x ^ 2 - 8 * x + 20) > 0 := h2 x
      apply div_neg_iff.mp at h4
      cases h4 with
      | inl h6 =>
        nlinarith
      | inr h7 =>
        nlinarith [h5]
    have h4 : m < 0 := by
      have h5 := h3 (-2)
      nlinarith
    have h6 := h3 1
    nlinarith
  · -- Second direction: if m < -1/2, then the set is equal to ⊤
    intro hm
    have h1 : ∀ x : ℝ, (x ^ 2 - 8 * x + 20) / (m * x ^ 2 + 2 * (m + 1) * x + 9 * m + 4) < 0 := by
      intro x
      have h2 : x ^ 2 - 8 * x + 20 > 0 := by
        nlinarith [sq_nonneg (x - 4)]
      have h3 : m * x ^ 2 + 2 * (m + 1) * x + 9 * m + 4 < 0 := by
        nlinarith [sq_nonneg (x + (m + 1)/m), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x + 2),
          mul_self_nonneg (m + 1/2), mul_self_nonneg (m - 1/4)]
      apply div_neg_of_pos_of_neg h2 h3
    simp [Set.ext_iff]
    intro x
    specialize h1 x
    linarith