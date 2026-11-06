import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_159524 {a b : ℝ} (ha : a < b) (F : ℝ → ℝ)
  (hF : F = λ x => (x - a) / (b - a)) :
  ∀ x, x ∈ Ioo a b ↔ ∃ r, r ∈ Ioo 0 1 ∧ x = (b - a) * r + a := by

  intro x
  constructor
  · -- Assume x ∈ (a, b)
    rintro ⟨hx1, hx2⟩
    use (x - a) / (b - a)
    constructor
    · -- Show r ∈ (0, 1)
      constructor
      · -- Show 0 < (x - a) / (b - a)
        apply div_pos
        all_goals linarith
      · -- Show (x - a) / (b - a) < 1
        have h1 : x - a < b - a := by linarith
        have h2 : (x - a) / (b - a) < (b - a) / (b - a) := by
          apply (div_lt_div_right (by linarith)).mpr
          linarith
        have h3 : (b - a) / (b - a) = 1 := by
          field_simp [show b - a ≠ 0 by linarith]
        linarith [h2, h3]
    · -- Show x = (b - a) * r + a
      field_simp [show b - a ≠ 0 by linarith]
      all_goals
        linarith
  · -- Assume ∃ r ∈ (0, 1), x = (b - a) * r + a
    rintro ⟨r, ⟨hr1, hr2⟩, hx⟩
    constructor
    · -- Show a < x
      nlinarith
    · -- Show x < b
      nlinarith
      all_goals linarith