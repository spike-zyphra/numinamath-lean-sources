import Mathlib

theorem algebra_264851 (x : ℝ) (hx : x ≠ -10 ∧ x ≠ 0) : 3 / (x + 10) = 1 / (2 * x) ↔ x = 2 := by
  constructor
  · -- Forward direction: If 3/(x + 10) = 1/(2 * x) then x = 2
    intro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : x + 10 ≠ 0 := by
      intro h2
      apply hx1
      linarith
    have h2 : 2 * x ≠ 0 := by
      intro h3
      have : x = 0 := by linarith
      tauto
    field_simp [(show x + 10 ≠ 0 by assumption), (show (2 * x) ≠ 0 by assumption)] at h
    have h3 : 5 * x = 10 := by linarith
    linarith
  · -- Backward direction: If x = 2 then 3/(x + 10) = 1/(2 * x)
    intro h_eq
    rw [h_eq]
    norm_num