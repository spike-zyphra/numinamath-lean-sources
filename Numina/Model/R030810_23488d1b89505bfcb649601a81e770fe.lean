import Mathlib

theorem algebra_11546 : {x : ℝ | x ^ 2 - 7 * x + 6 < 0} = Set.Ioo 1 6 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- Assume x^2 - 7 * x + 6 < 0, prove 1 < x ∧ x < 6
    intro h
    have h1 : x ^ 2 - 7 * x + 6 < 0 := h
    have h2 : x ^ 2 - 7 * x + 6 = (x - 1) * (x - 6) := by
      ring_nf
    rw [h2] at h1
    cases mul_neg_iff.mp h1 with
    | inl h3 =>
      constructor
      · linarith
      · linarith
    | inr h4 =>
      linarith
  · -- Assume 1 < x ∧ x < 6, prove x^2 - 7 * x + 6 < 0
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 - 7 * x + 6 = (x - 1) * (x - 6) := by
      ring_nf
    rw [h3]
    have h4 : x - 1 > 0 := by linarith
    have h5 : x - 6 < 0 := by linarith
    exact mul_neg_of_pos_of_neg h4 h5