import Mathlib

theorem algebra_21136 {A B : ℝ} (hA : A ∈ Set.Ioo 0 π) (hB : B ∈ Set.Ioo 0 π)
    (hAB : A + B = π) (hA' : A / B = 7 / 23) :
    (π - A) / (π - B) = 23 / 7 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  have h1 : π - A = B := by
    linarith
  have h2 : π - B = A := by
    linarith
  have h3 : B ≠ 0 := by
    linarith
  have h4 : A ≠ 0 := by
    linarith
  have h5 : (π - A) / (π - B) = B / A := by
    rw [show π - A = B by linarith, show π - B = A by linarith]
  have h8 : B / A = 23 / 7 := by
    have h9 : A / B = 7 / 23 := hA'
    field_simp [show B ≠ 0 by linarith, show A ≠ 0 by linarith] at h9 ⊢
    linarith
  rw [h5]
  exact h8