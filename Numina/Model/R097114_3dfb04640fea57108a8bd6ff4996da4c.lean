import Mathlib

theorem algebra_310608 {a b c : ℝ} (habc : a ≠ b ∧ b ≠ c ∧ c ≠ a) :
    (2 * b - a - c) / ((a - b) * (b - c)) +
    (2 * c - a - b) / ((b - c) * (c - a)) +
    (2 * a - b - c) / ((c - a) * (a - b)) = 0 := by
  rcases habc with ⟨hab1, hab2, hab3⟩
  have h1 : a - b ≠ 0 := by
    intro h
    apply hab1
    linarith
  have h2 : b - c ≠ 0 := by
    intro h
    apply hab2
    linarith
  have h3 : c - a ≠ 0 := by
    intro h
    apply hab3
    linarith
  field_simp [h1, h2, h3]
  ring