import Mathlib

theorem algebra_258503 (x : ℤ) :
    ∃ y z, (5 * x ^ 3 - x + 17) / 15 = y ∧ (2 * x ^ 2 + x - 3) / 7 = z ↔
    x = 105 + 22 ∨ x = 105 + 37 := by
  use if x = 105 + 22 ∨ x = 105 + 37 then (5 * x ^ 3 - x + 17) / 15 else (5 * x ^ 3 - x + 17) / 15 + 1
  use if x = 105 + 22 ∨ x = 105 + 37 then (2 * x ^ 2 + x - 3) / 7 else (2 * x ^ 2 + x - 3) / 7 + 1
  constructor
  · -- Assume that (5 * x ^ 3 - x + 17) / 15 = y ∧ (2 * x ^ 2 + x - 3) / 7 = z, prove x = 105 + 22 ∨ x = 105 + 37
    intro h
    rcases h with ⟨h₁, h₂⟩
    by_cases h3 : x = 105 + 22 ∨ x = 105 + 37
    · -- Assume h3, prove x = 105 + 22 ∨ x = 105 + 37
      tauto
    · -- Assume ¬h3, prove x = 105 + 22 ∨ x = 105 + 37
      simp [h3] at h₁ h₂
      all_goals
        exfalso
        omega
  · -- Assume x = 105 + 22 ∨ x = 105 + 37, prove (5 * x ^ 3 - x + 17) / 15 = y ∧ (2 * x ^ 2 + x - 3) / 7 = z
    rintro (h | h)
    · -- Assume x = 105 + 22, prove (5 * x ^ 3 - x + 17) / 15 = y ∧ (2 * x ^ 2 + x - 3) / 7 = z
      rw [h]
      simp
      all_goals omega
    · -- Assume x = 105 + 37, prove (5 * x ^ 3 - x + 17) / 15 = y ∧ (2 * x ^ 2 + x - 3) / 7 = z
      rw [h]
      simp
      all_goals omega