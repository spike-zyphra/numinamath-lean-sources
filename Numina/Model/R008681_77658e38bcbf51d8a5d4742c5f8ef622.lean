import Mathlib

theorem algebra_9137 : {x | x ^ 2 + 2 * x < 3} = {x | -3 < x ∧ x < 1} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- First direction: If x^2 + 2 * x < 3 Then (-3 < x ∧ x < 1)
    intro h
    have h1 : x^2 + 2*x - 3 < 0 := by linarith
    have h2 : x ^ 2 + 2 * x - 3 = (x + 3) * (x - 1) := by ring
    rw [h2] at h1
    cases mul_neg_iff.mp h1 with
    | inl h3 =>
      constructor
      · linarith
      · linarith
    | inr h3 =>
      linarith
  · -- Second direction: If (-3 < x ∧ x < 1) Then x^2 + 2 * x < 3
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 + 2 * x - 3 < 0 := by
      have h3' : x ^ 2 + 2 * x - 3 = (x + 3) * (x - 1) := by ring
      rw [h3']
      have h4 : (x + 3) > 0 := by linarith
      have h5 : (x - 1) < 0 := by linarith
      exact mul_neg_of_pos_of_neg h4 h5
    linarith