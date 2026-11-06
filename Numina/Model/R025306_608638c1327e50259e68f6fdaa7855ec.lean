import Mathlib

theorem algebra_603629 {a c : ℝ} (ha : a ≠ 0) (h : ∀ x, a * x ^ 2 - x - c > 0 ↔ -2 < x ∧ x < 1) :
    ∀ x, a * (-x) ^ 2 - (-x) - c > 0 ↔ -1 < x ∧ x < 2 := by 
  intro x
  have h1 : a * (-x) ^ 2 - (-x) - c > 0 ↔ a * x ^ 2 + x - c > 0 := by 
    have h2 : a * (-x) ^ 2 - (-x) - c = a * x ^ 2 + x - c := by
      ring_nf
    rw [h2]
    all_goals ring_nf
  rw [h1]
  have h2 : a * x ^ 2 + x - c > 0 ↔ -1 < x ∧ x < 2 := by
    have h3 : a * x ^ 2 + x - c > 0 ↔ a * (-x) ^ 2 - (-x) - c > 0 := by 
      have h4 : a * (-x) ^ 2 - (-x) - c = a * x ^ 2 + x - c := by
        ring_nf
      rw [h4]
    have h4 := h (-x)
    have h5 : (-2 < -x ∧ -x < 1) ↔ (-1 < x ∧ x < 2) := by
      constructor
      · -- Assume (-2 < -x ∧ -x < 1), prove (-1 < x ∧ x < 2)
        rintro ⟨h1, h2⟩
        constructor
        · linarith
        · linarith
      · -- Assume (-1 < x ∧ x < 2), prove (-2 < -x ∧ -x < 1)
        rintro ⟨h1, h2⟩
        constructor
        · linarith
        · linarith
    have h5' : a * (-x) ^ 2 - (-x) - c > 0 ↔ (-2 < -x ∧ -x < 1) := by 
      simpa using h4
    have h3' : a * (-x) ^ 2 - (-x) - c > 0 ↔ (-1 < x ∧ x < 2) := by
      rw [h5'] 
      rw [h5]
      all_goals tauto
    rw [show a * x ^ 2 + x - c > 0 ↔ a * (-x) ^ 2 - (-x) - c > 0 by rw [h3]]
    all_goals rw [h3']
    all_goals tauto
  exact h2