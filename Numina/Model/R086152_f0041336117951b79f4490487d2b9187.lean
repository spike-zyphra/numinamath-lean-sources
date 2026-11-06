import Mathlib

theorem algebra_311369 {a b c : ℝ} (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (b - c) / ((a - b) * (a - c)) + (c - a) / ((b - c) * (b - a)) +
    (a - b) / ((c - a) * (c - b)) = 2 / (a - b) + 2 / (b - c) + 2 / (c - a) := by
  rcases habc with ⟨h1, h2, h3⟩
  have h4 : b - c ≠ 0 := by
    intro h
    apply h3
    linarith
  have h5 : a - b ≠ 0 := by
    intro h
    apply h1
    linarith
  have h6 : a - c ≠ 0 := by
    intro h
    apply h2
    linarith
  have h7 : b - a ≠ 0 := by
    intro h
    apply h1
    linarith
  have h8 : c - a ≠ 0 := by
    intro h
    apply h2
    linarith
  have h9 : c - b ≠ 0 := by
    intro h
    apply h3
    linarith
  field_simp [h5, h6, h4, h7, h8, h9]
  ring