import Mathlib

theorem algebra_280705 {l w : ℕ} (hl : l > 0) (hw : w > 0)
    (h₀ : l * w = 48) (h₁ : 2 * (l + w) = 32) :
    max l w - min l w = 8 := by

  have h2 : l + w = 16 := by
    linarith

  have h3 : l ≤ 16 := by
    omega
  have h4 : w ≤ 16 := by
    omega

  interval_cases l <;> omega