import Mathlib

theorem number_theory_279785 (A B : ℝ) (hA : A > 0) (hB : B > 0)
    (hA1 : ∃ x, A = x / 10^6) (hB1 : ∃ x, B = x / 10^12) :
    ∃ x, A + B = x / 10^12 ∨ A + B = x / 10^4 := by 
  rcases hA1 with ⟨x, hAx⟩
  rcases hB1 with ⟨y, hBy⟩
  use (x * 10^6 + y)
  left
  rw [hAx, hBy]
  field_simp
  <;> ring